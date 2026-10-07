import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell980_leftExp :
    (34041660827 / 10000000000 : ℝ) ≤ Real.exp (49 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (49 / 40 : ℝ) (259755854281 / 250000000000 : ℝ)
    (34041660827 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell980_rightExp :
    Real.exp (981 / 800 : ℝ) ≤ (34084239511 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (981 / 800 : ℝ) (103906400477 / 100000000000 : ℝ)
    (34084239511 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell980_denomUpper :
    Real.exp (104016308258081023 / 10000000000000000 : ℝ) ≤ (329132577210637 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (104016308258081023 / 10000000000000000 : ℝ)
    (1384101182557 / 1000000000000 : ℝ) (329132577210637 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell980_denomLower :
    (324656677186463 / 10000000000 : ℝ) ≤ Real.exp (12984923040102073 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (12984923040102073 / 1250000000000000 : ℝ) (8646931687 /
    6250000000 : ℝ) (324656677186463 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell980_product_lower :
    (13368126165102073 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (49 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell980_leftExp
    (by norm_num : (0 : ℝ) ≤ (34041660827 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell980_product_upper :
    Real.pi * Real.exp (981 / 800 : ℝ) ≤ (107078808258081023 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell980_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell980_endpointLower :
    (239005447 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (49 / 80 : ℝ) (981 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13368126165102073 / 1250000000000000 : ℝ) (Real.pi * Real.exp (49 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell980_product_lower
  have hD : Real.exp (Real.pi * Real.exp (981 / 800 : ℝ) - (49 / 160 : ℝ)) ≤
      (329132577210637 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell980_denomUpper
    linarith [hpThetaJensenCell980_product_upper]
  have hi : (1 / (329132577210637 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (981 / 800 : ℝ) - (49 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (329132577210637 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (329132577210637 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((49 / 160 : ℝ) - Real.pi * Real.exp (981 / 800 : ℝ)) := by
    rw [show (49 / 160 : ℝ) - Real.pi * Real.exp (981 / 800 : ℝ) =
      -(Real.pi * Real.exp (981 / 800 : ℝ) - (49 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (49 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (49 / 40 : ℝ)) := by
    have h := hpThetaJensenCell980_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (329132577210637 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell980_endpointUpper :
    hpThetaJensenKernelEndpointUpper (49 / 80 : ℝ) (981 / 1600 : ℝ) ≤ (121798263 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (981 / 800 : ℝ)) (107078808258081023 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (981 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell980_product_upper
  have hD : (324656677186463 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (49 / 40 : ℝ) - (981 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell980_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell980_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (49 / 40 : ℝ) - (981 / 3200 : ℝ)) ≤
      (1 / (324656677186463 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (324656677186463 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((981 / 3200 : ℝ) - Real.pi * Real.exp (49 / 40 : ℝ)) ≤
      (2 / (324656677186463 / 10000000000 : ℝ) : ℝ) := by
    rw [show (981 / 3200 : ℝ) - Real.pi * Real.exp (49 / 40 : ℝ) =
      -(Real.pi * Real.exp (49 / 40 : ℝ) - (981 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (107078808258081023 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (107078808258081023 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell980_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (49 / 80 : ℝ) (981 / 1600 : ℝ)) :
    (239005447 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (121798263 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell980_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell980_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell981_leftExp :
    (34084239509 / 10000000000 : ℝ) ≤ Real.exp (981 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (981 / 800 : ℝ) (1039064004769 / 1000000000000 : ℝ)
    (34084239509 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell981_rightExp :
    Real.exp (491 / 400 : ℝ) ≤ (682537429 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (491 / 400 : ℝ) (519552297 / 500000000 : ℝ)
    (682537429 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell981_denomUpper :
    Real.exp (2082942309184397 / 200000000000000 : ℝ) ≤ (166733074831311 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (2082942309184397 / 200000000000000 : ℝ) (346166770179 /
    250000000000 : ℝ) (166733074831311 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell981_denomLower :
    (164462906141287 / 5000000000 : ℝ) ≤ Real.exp (13001253020944791 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (13001253020944791 / 1250000000000000 : ℝ) (43252312567 /
    31250000000 : ℝ) (164462906141287 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell981_product_lower :
    (13384846770944791 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (981 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell981_leftExp
    (by norm_num : (0 : ℝ) ≤ (34084239509 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell981_product_upper :
    Real.pi * Real.exp (491 / 400 : ℝ) ≤ (2144254809184397 / 200000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell981_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell981_endpointLower :
    (378461 / 16000000 : ℝ) ≤ hpThetaTraceEndpointLower (981 / 1600 : ℝ) (491 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13384846770944791 / 1250000000000000 : ℝ) (Real.pi * Real.exp (981 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell981_product_lower
  have hD : Real.exp (Real.pi * Real.exp (491 / 400 : ℝ) - (981 / 3200 : ℝ)) ≤
      (166733074831311 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell981_denomUpper
    linarith [hpThetaJensenCell981_product_upper]
  have hi : (1 / (166733074831311 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (491 / 400 : ℝ) - (981 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (166733074831311 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (166733074831311 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((981 / 3200 : ℝ) - Real.pi * Real.exp (491 / 400 : ℝ)) := by
    rw [show (981 / 3200 : ℝ) - Real.pi * Real.exp (491 / 400 : ℝ) =
      -(Real.pi * Real.exp (491 / 400 : ℝ) - (981 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (981 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (981 / 800 : ℝ)) := by
    have h := hpThetaJensenCell981_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (166733074831311 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell981_endpointUpper :
    hpThetaJensenKernelEndpointUpper (981 / 1600 : ℝ) (491 / 800 : ℝ) ≤ (60271443 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (491 / 400 : ℝ)) (2144254809184397 / 200000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (491 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell981_product_upper
  have hD : (164462906141287 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (981 / 800 : ℝ) - (491 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell981_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell981_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (981 / 800 : ℝ) - (491 / 1600 : ℝ)) ≤
      (1 / (164462906141287 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (164462906141287 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((491 / 1600 : ℝ) - Real.pi * Real.exp (981 / 800 : ℝ)) ≤
      (2 / (164462906141287 / 5000000000 : ℝ) : ℝ) := by
    rw [show (491 / 1600 : ℝ) - Real.pi * Real.exp (981 / 800 : ℝ) =
      -(Real.pi * Real.exp (981 / 800 : ℝ) - (491 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2144254809184397 / 200000000000000 : ℝ) ^ 2 - 6 *
      (2144254809184397 / 200000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell981_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (981 / 1600 : ℝ) (491 / 800 : ℝ)) :
    (378461 / 16000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (60271443 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell981_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell981_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell982_leftExp :
    (4265858931 / 1250000000 : ℝ) ≤ Real.exp (491 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (491 / 400 : ℝ) (1039104593999 / 1000000000000 : ℝ)
    (4265858931 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell982_rightExp :
    Real.exp (983 / 800 : ℝ) ≤ (4271194589 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (983 / 800 : ℝ) (64946574051 / 62500000000 : ℝ)
    (4271194589 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell982_denomUpper :
    Real.exp (13034761272440277 / 1250000000000000 : ℝ) ≤ (168931220268297 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (13034761272440277 / 1250000000000000 : ℝ) (1385233935413
    / 1000000000000 : ℝ) (168931220268297 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell982_denomLower :
    (20828541307229 / 625000000 : ℝ) ≤ Real.exp (1627200489469769 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1627200489469769 / 156250000000000 : ℝ) (692319944503 /
    500000000000 : ℝ) (20828541307229 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell982_product_lower :
    (1675198536344769 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (491 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell982_leftExp
    (by norm_num : (0 : ℝ) ≤ (4265858931 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell982_product_upper :
    Real.pi * Real.exp (983 / 800 : ℝ) ≤ (13418355022440277 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell982_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell982_endpointLower :
    (58523071 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (491 / 800 : ℝ) (983 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1675198536344769 / 156250000000000 : ℝ) (Real.pi * Real.exp (491 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell982_product_lower
  have hD : Real.exp (Real.pi * Real.exp (983 / 800 : ℝ) - (491 / 1600 : ℝ)) ≤
      (168931220268297 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell982_denomUpper
    linarith [hpThetaJensenCell982_product_upper]
  have hi : (1 / (168931220268297 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (983 / 800 : ℝ) - (491 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (168931220268297 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (168931220268297 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((491 / 1600 : ℝ) - Real.pi * Real.exp (983 / 800 : ℝ)) := by
    rw [show (491 / 1600 : ℝ) - Real.pi * Real.exp (983 / 800 : ℝ) =
      -(Real.pi * Real.exp (983 / 800 : ℝ) - (491 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (491 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (491 / 400 : ℝ)) := by
    have h := hpThetaJensenCell982_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (168931220268297 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell982_endpointUpper :
    hpThetaJensenKernelEndpointUpper (491 / 800 : ℝ) (983 / 1600 : ℝ) ≤ (47719367 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (983 / 800 : ℝ)) (13418355022440277 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (983 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell982_product_upper
  have hD : (20828541307229 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (491 / 400 : ℝ) - (983 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell982_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell982_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (491 / 400 : ℝ) - (983 / 3200 : ℝ)) ≤
      (1 / (20828541307229 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (20828541307229 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((983 / 3200 : ℝ) - Real.pi * Real.exp (491 / 400 : ℝ)) ≤
      (2 / (20828541307229 / 625000000 : ℝ) : ℝ) := by
    rw [show (983 / 3200 : ℝ) - Real.pi * Real.exp (491 / 400 : ℝ) =
      -(Real.pi * Real.exp (491 / 400 : ℝ) - (983 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (13418355022440277 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (13418355022440277 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell982_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (491 / 800 : ℝ) (983 / 1600 : ℝ)) :
    (58523071 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (47719367 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell982_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell982_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell983_leftExp :
    (3416955671 / 1000000000 : ℝ) ≤ Real.exp (983 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (983 / 800 : ℝ) (207829036963 / 200000000000 : ℝ)
    (3416955671 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell983_rightExp :
    Real.exp (123 / 100 : ℝ) ≤ (8553073841 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (123 / 100 : ℝ) (519592888609 / 500000000000 : ℝ)
    (8553073841 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell983_denomUpper :
    Real.exp (26102308157368713 / 2500000000000000 : ℝ) ≤ (21395152009061 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (26102308157368713 / 2500000000000000 : ℝ) (1385801748543
    / 1000000000000 : ℝ) (21395152009061 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell983_denomLower :
    (337650188524597 / 10000000000 : ℝ) ≤ Real.exp (1303397575046029 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1303397575046029 / 125000000000000 : ℝ) (692603366193 /
    500000000000 : ℝ) (337650188524597 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell983_product_lower :
    (1341835075046029 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (983 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell983_leftExp
    (by norm_num : (0 : ℝ) ≤ (3416955671 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell983_product_upper :
    Real.pi * Real.exp (123 / 100 : ℝ) ≤ (26870276907368713 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell983_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell983_endpointLower :
    (115833889 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (983 / 1600 : ℝ) (123 / 200 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1341835075046029 / 125000000000000 : ℝ) (Real.pi * Real.exp (983 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell983_product_lower
  have hD : Real.exp (Real.pi * Real.exp (123 / 100 : ℝ) - (983 / 3200 : ℝ)) ≤
      (21395152009061 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell983_denomUpper
    linarith [hpThetaJensenCell983_product_upper]
  have hi : (1 / (21395152009061 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (123 / 100 : ℝ) - (983 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (21395152009061 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (21395152009061 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((983 / 3200 : ℝ) - Real.pi * Real.exp (123 / 100 : ℝ)) := by
    rw [show (983 / 3200 : ℝ) - Real.pi * Real.exp (123 / 100 : ℝ) =
      -(Real.pi * Real.exp (123 / 100 : ℝ) - (983 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (983 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (983 / 800 : ℝ)) := by
    have h := hpThetaJensenCell983_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (21395152009061 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell983_endpointUpper :
    hpThetaJensenKernelEndpointUpper (983 / 1600 : ℝ) (123 / 200 : ℝ) ≤ (236129567 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (123 / 100 : ℝ)) (26870276907368713 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (123 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell983_product_upper
  have hD : (337650188524597 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (983 / 800 : ℝ) - (123 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell983_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell983_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (983 / 800 : ℝ) - (123 / 400 : ℝ)) ≤
      (1 / (337650188524597 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (337650188524597 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((123 / 400 : ℝ) - Real.pi * Real.exp (983 / 800 : ℝ)) ≤
      (2 / (337650188524597 / 10000000000 : ℝ) : ℝ) := by
    rw [show (123 / 400 : ℝ) - Real.pi * Real.exp (983 / 800 : ℝ) =
      -(Real.pi * Real.exp (983 / 800 : ℝ) - (123 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (26870276907368713 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (26870276907368713 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell983_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (983 / 1600 : ℝ) (123 / 200 : ℝ)) :
    (115833889 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (236129567 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell983_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell983_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell984_leftExp :
    (17106147681 / 5000000000 : ℝ) ≤ Real.exp (123 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (123 / 100 : ℝ) (1039185777217 / 1000000000000 : ℝ)
    (17106147681 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell984_rightExp :
    Real.exp (197 / 160 : ℝ) ≤ (34255087473 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (197 / 160 : ℝ) (207845274241 / 200000000000 : ℝ)
    (34255087473 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell984_denomUpper :
    Real.exp (104540543019564489 / 10000000000000000 : ℝ) ≤ (346847123287239 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (104540543019564489 / 10000000000000000 : ℝ)
    (1386370522007 / 1000000000000 : ℝ) (346847123287239 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell984_denomLower :
    (17105368840983 / 500000000 : ℝ) ≤ Real.exp (6525184275681019 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6525184275681019 / 625000000000000 : ℝ) (1385774534181 /
    1000000000000 : ℝ) (17105368840983 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell984_product_lower :
    (6717567088181019 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (123 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell984_leftExp
    (by norm_num : (0 : ℝ) ≤ (17106147681 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell984_product_upper :
    Real.pi * Real.exp (197 / 160 : ℝ) ≤ (107615543019564489 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell984_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell984_endpointLower :
    (45852893 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (123 / 200 : ℝ) (197 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6717567088181019 / 625000000000000 : ℝ) (Real.pi * Real.exp (123 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell984_product_lower
  have hD : Real.exp (Real.pi * Real.exp (197 / 160 : ℝ) - (123 / 400 : ℝ)) ≤
      (346847123287239 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell984_denomUpper
    linarith [hpThetaJensenCell984_product_upper]
  have hi : (1 / (346847123287239 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (197 / 160 : ℝ) - (123 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (346847123287239 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (346847123287239 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((123 / 400 : ℝ) - Real.pi * Real.exp (197 / 160 : ℝ)) := by
    rw [show (123 / 400 : ℝ) - Real.pi * Real.exp (197 / 160 : ℝ) =
      -(Real.pi * Real.exp (197 / 160 : ℝ) - (123 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (123 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (123 / 100 : ℝ)) := by
    have h := hpThetaJensenCell984_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (346847123287239 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell984_endpointUpper :
    hpThetaJensenKernelEndpointUpper (123 / 200 : ℝ) (197 / 320 : ℝ) ≤ (14605239 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (197 / 160 : ℝ)) (107615543019564489 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (197 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell984_product_upper
  have hD : (17105368840983 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (123 / 100 : ℝ) - (197 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell984_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell984_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (123 / 100 : ℝ) - (197 / 640 : ℝ)) ≤
      (1 / (17105368840983 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (17105368840983 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((197 / 640 : ℝ) - Real.pi * Real.exp (123 / 100 : ℝ)) ≤
      (2 / (17105368840983 / 500000000 : ℝ) : ℝ) := by
    rw [show (197 / 640 : ℝ) - Real.pi * Real.exp (123 / 100 : ℝ) =
      -(Real.pi * Real.exp (123 / 100 : ℝ) - (197 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (107615543019564489 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (107615543019564489 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell984_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (123 / 200 : ℝ) (197 / 320 : ℝ)) :
    (45852893 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (14605239 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell984_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell984_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell985_leftExp :
    (34255087471 / 10000000000 : ℝ) ≤ Real.exp (197 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (197 / 160 : ℝ) (259806592801 / 250000000000 : ℝ)
    (34255087471 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell985_rightExp :
    Real.exp (493 / 400 : ℝ) ≤ (6859586621 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (493 / 400 : ℝ) (519633483389 / 500000000000 : ℝ)
    (6859586621 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell985_denomUpper :
    Real.exp (20934404311427253 / 2000000000000000 : ℝ) ≤ (351437529406331 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (20934404311427253 / 2000000000000000 : ℝ) (277388051539
    / 200000000000 : ℝ) (351437529406331 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell985_denomLower :
    (346629223956629 / 10000000000 : ℝ) ≤ Real.exp (13066782344774229 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (13066782344774229 / 1250000000000000 : ℝ) (138634329629
    / 100000000000 : ℝ) (346629223956629 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell985_product_lower :
    (13451938594774229 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (197 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell985_leftExp
    (by norm_num : (0 : ℝ) ≤ (34255087471 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell985_product_upper :
    Real.pi * Real.exp (493 / 400 : ℝ) ≤ (21550029311427253 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell985_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell985_endpointLower :
    (113441101 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (197 / 320 : ℝ) (493 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13451938594774229 / 1250000000000000 : ℝ) (Real.pi * Real.exp (197 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell985_product_lower
  have hD : Real.exp (Real.pi * Real.exp (493 / 400 : ℝ) - (197 / 640 : ℝ)) ≤
      (351437529406331 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell985_denomUpper
    linarith [hpThetaJensenCell985_product_upper]
  have hi : (1 / (351437529406331 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (493 / 400 : ℝ) - (197 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (351437529406331 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (351437529406331 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((197 / 640 : ℝ) - Real.pi * Real.exp (493 / 400 : ℝ)) := by
    rw [show (197 / 640 : ℝ) - Real.pi * Real.exp (493 / 400 : ℝ) =
      -(Real.pi * Real.exp (493 / 400 : ℝ) - (197 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (197 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (197 / 160 : ℝ)) := by
    have h := hpThetaJensenCell985_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (351437529406331 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell985_endpointUpper :
    hpThetaJensenKernelEndpointUpper (197 / 320 : ℝ) (493 / 800 : ℝ) ≤ (115629731 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (493 / 400 : ℝ)) (21550029311427253 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (493 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell985_product_upper
  have hD : (346629223956629 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (197 / 160 : ℝ) - (493 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell985_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell985_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (197 / 160 : ℝ) - (493 / 1600 : ℝ)) ≤
      (1 / (346629223956629 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (346629223956629 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((493 / 1600 : ℝ) - Real.pi * Real.exp (197 / 160 : ℝ)) ≤
      (2 / (346629223956629 / 10000000000 : ℝ) : ℝ) := by
    rw [show (493 / 1600 : ℝ) - Real.pi * Real.exp (197 / 160 : ℝ) =
      -(Real.pi * Real.exp (197 / 160 : ℝ) - (493 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (21550029311427253 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (21550029311427253 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell985_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (197 / 320 : ℝ) (493 / 800 : ℝ)) :
    (113441101 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (115629731 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell985_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell985_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell986_leftExp :
    (34297933103 / 10000000000 : ℝ) ≤ Real.exp (493 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (493 / 400 : ℝ) (1039266966777 / 1000000000000 : ℝ)
    (34297933103 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell986_rightExp :
    Real.exp (987 / 800 : ℝ) ≤ (4292604041 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (987 / 800 : ℝ) (1039307563937 / 1000000000000 : ℝ)
    (4292604041 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell986_denomUpper :
    Real.exp (13100458556977313 / 1250000000000000 : ℝ) ≤ (71218936644913 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (13100458556977313 / 1250000000000000 : ℝ) (173438869691
    / 125000000000 : ℝ) (71218936644913 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell986_denomLower :
    (175608372373897 / 5000000000 : ℝ) ≤ Real.exp (13083217156614997 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (13083217156614997 / 1250000000000000 : ℝ) (346728255151
    / 250000000000 : ℝ) (175608372373897 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell986_product_lower :
    (13468764031614997 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (493 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell986_leftExp
    (by norm_num : (0 : ℝ) ≤ (34297933103 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell986_product_upper :
    Real.pi * Real.exp (987 / 800 : ℝ) ≤ (13485614806977313 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell986_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell986_endpointLower :
    (224520847 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (493 / 800 : ℝ) (987 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13468764031614997 / 1250000000000000 : ℝ) (Real.pi * Real.exp (493 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell986_product_lower
  have hD : Real.exp (Real.pi * Real.exp (987 / 800 : ℝ) - (493 / 1600 : ℝ)) ≤
      (71218936644913 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell986_denomUpper
    linarith [hpThetaJensenCell986_product_upper]
  have hi : (1 / (71218936644913 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (987 / 800 : ℝ) - (493 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (71218936644913 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (71218936644913 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((493 / 1600 : ℝ) - Real.pi * Real.exp (987 / 800 : ℝ)) := by
    rw [show (493 / 1600 : ℝ) - Real.pi * Real.exp (987 / 800 : ℝ) =
      -(Real.pi * Real.exp (987 / 800 : ℝ) - (493 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (493 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (493 / 400 : ℝ)) := by
    have h := hpThetaJensenCell986_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (71218936644913 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell986_endpointUpper :
    hpThetaJensenKernelEndpointUpper (493 / 800 : ℝ) (987 / 1600 : ℝ) ≤ (14303521 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (987 / 800 : ℝ)) (13485614806977313 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (987 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell986_product_upper
  have hD : (175608372373897 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (493 / 400 : ℝ) - (987 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell986_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell986_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (493 / 400 : ℝ) - (987 / 3200 : ℝ)) ≤
      (1 / (175608372373897 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (175608372373897 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((987 / 3200 : ℝ) - Real.pi * Real.exp (493 / 400 : ℝ)) ≤
      (2 / (175608372373897 / 5000000000 : ℝ) : ℝ) := by
    rw [show (987 / 3200 : ℝ) - Real.pi * Real.exp (493 / 400 : ℝ) =
      -(Real.pi * Real.exp (493 / 400 : ℝ) - (987 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (13485614806977313 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (13485614806977313 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell986_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (493 / 800 : ℝ) (987 / 1600 : ℝ)) :
    (224520847 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (14303521 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell986_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell986_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell987_leftExp :
    (17170416163 / 5000000000 : ℝ) ≤ Real.exp (987 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (987 / 800 : ℝ) (32478361373 / 31250000000 : ℝ)
    (17170416163 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell987_rightExp :
    Real.exp (247 / 200 : ℝ) ≤ (4297973151 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (247 / 200 : ℝ) (1039348162681 / 1000000000000 : ℝ)
    (4297973151 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell987_denomUpper :
    Real.exp (13116935490369543 / 1250000000000000 : ℝ) ≤ (180409817298117 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (13116935490369543 / 1250000000000000 : ℝ) (694041311701
    / 500000000000 : ℝ) (180409817298117 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell987_denomLower :
    (7117419425159 / 200000000 : ℝ) ≤ Real.exp (6549836506793937 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6549836506793937 / 625000000000000 : ℝ) (1387483709043 /
    1000000000000 : ℝ) (7117419425159 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell987_product_lower :
    (6742805256793937 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (987 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell987_leftExp
    (by norm_num : (0 : ℝ) ≤ (17170416163 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell987_product_upper :
    Real.pi * Real.exp (247 / 200 : ℝ) ≤ (13502482365369543 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell987_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell987_endpointLower :
    (111090129 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (987 / 1600 : ℝ) (247 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6742805256793937 / 625000000000000 : ℝ) (Real.pi * Real.exp (987 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell987_product_lower
  have hD : Real.exp (Real.pi * Real.exp (247 / 200 : ℝ) - (987 / 3200 : ℝ)) ≤
      (180409817298117 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell987_denomUpper
    linarith [hpThetaJensenCell987_product_upper]
  have hi : (1 / (180409817298117 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (247 / 200 : ℝ) - (987 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (180409817298117 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (180409817298117 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((987 / 3200 : ℝ) - Real.pi * Real.exp (247 / 200 : ℝ)) := by
    rw [show (987 / 3200 : ℝ) - Real.pi * Real.exp (247 / 200 : ℝ) =
      -(Real.pi * Real.exp (247 / 200 : ℝ) - (987 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (987 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (987 / 800 : ℝ)) := by
    have h := hpThetaJensenCell987_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (180409817298117 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell987_endpointUpper :
    hpThetaJensenKernelEndpointUpper (987 / 1600 : ℝ) (247 / 400 : ℝ) ≤ (113237151 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (247 / 200 : ℝ)) (13502482365369543 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (247 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell987_product_upper
  have hD : (7117419425159 / 200000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (987 / 800 : ℝ) - (247 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell987_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell987_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (987 / 800 : ℝ) - (247 / 800 : ℝ)) ≤
      (1 / (7117419425159 / 200000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (7117419425159 / 200000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((247 / 800 : ℝ) - Real.pi * Real.exp (987 / 800 : ℝ)) ≤
      (2 / (7117419425159 / 200000000 : ℝ) : ℝ) := by
    rw [show (247 / 800 : ℝ) - Real.pi * Real.exp (987 / 800 : ℝ) =
      -(Real.pi * Real.exp (987 / 800 : ℝ) - (247 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (13502482365369543 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (13502482365369543 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell987_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (987 / 1600 : ℝ) (247 / 400 : ℝ)) :
    (111090129 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (113237151 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell987_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell987_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell988_leftExp :
    (17191892603 / 5000000000 : ℝ) ≤ Real.exp (247 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (247 / 200 : ℝ) (25983704067 / 25000000000 : ℝ)
    (17191892603 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell988_rightExp :
    Real.exp (989 / 800 : ℝ) ≤ (34426791813 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (989 / 800 : ℝ) (259847190753 / 250000000000 : ℝ)
    (34426791813 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell988_denomUpper :
    Real.exp (105067468172178109 / 10000000000000000 : ℝ) ≤ (365613451282611 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (105067468172178109 / 10000000000000000 : ℝ)
    (277731051449 / 200000000000 : ℝ) (365613451282611 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell988_denomLower :
    (90148238172327 / 2500000000 : ℝ) ≤ Real.exp (6558074970805497 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6558074970805497 / 625000000000000 : ℝ) (86753460219 /
    62500000000 : ℝ) (90148238172327 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell988_product_lower :
    (6751239033305497 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (247 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell988_leftExp
    (by norm_num : (0 : ℝ) ≤ (17191892603 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell988_product_upper :
    Real.pi * Real.exp (989 / 800 : ℝ) ≤ (108154968172178109 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell988_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell988_endpointLower :
    (109930147 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (247 / 400 : ℝ) (989 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6751239033305497 / 625000000000000 : ℝ) (Real.pi * Real.exp (247 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell988_product_lower
  have hD : Real.exp (Real.pi * Real.exp (989 / 800 : ℝ) - (247 / 800 : ℝ)) ≤
      (365613451282611 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell988_denomUpper
    linarith [hpThetaJensenCell988_product_upper]
  have hi : (1 / (365613451282611 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (989 / 800 : ℝ) - (247 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (365613451282611 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (365613451282611 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((247 / 800 : ℝ) - Real.pi * Real.exp (989 / 800 : ℝ)) := by
    rw [show (247 / 800 : ℝ) - Real.pi * Real.exp (989 / 800 : ℝ) =
      -(Real.pi * Real.exp (989 / 800 : ℝ) - (247 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (247 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (247 / 200 : ℝ)) := by
    have h := hpThetaJensenCell988_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (365613451282611 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell988_endpointUpper :
    hpThetaJensenKernelEndpointUpper (247 / 400 : ℝ) (989 / 1600 : ℝ) ≤ (112056609 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (989 / 800 : ℝ)) (108154968172178109 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (989 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell988_product_upper
  have hD : (90148238172327 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (247 / 200 : ℝ) - (989 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell988_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell988_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (247 / 200 : ℝ) - (989 / 3200 : ℝ)) ≤
      (1 / (90148238172327 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (90148238172327 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((989 / 3200 : ℝ) - Real.pi * Real.exp (247 / 200 : ℝ)) ≤
      (2 / (90148238172327 / 2500000000 : ℝ) : ℝ) := by
    rw [show (989 / 3200 : ℝ) - Real.pi * Real.exp (247 / 200 : ℝ) =
      -(Real.pi * Real.exp (247 / 200 : ℝ) - (989 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (108154968172178109 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (108154968172178109 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell988_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (247 / 400 : ℝ) (989 / 1600 : ℝ)) :
    (109930147 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (112056609 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell988_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell988_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell989_leftExp :
    (34426791811 / 10000000000 : ℝ) ≤ Real.exp (989 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (989 / 800 : ℝ) (1039388763011 / 1000000000000 : ℝ)
    (34426791811 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell989_rightExp :
    Real.exp (99 / 80 : ℝ) ≤ (3446985221 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (99 / 80 : ℝ) (1039429364929 / 1000000000000 : ℝ)
    (3446985221 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell989_denomUpper :
    Real.exp (10519962141397053 / 1000000000000000 : ℝ) ≤ (370477218907367 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (10519962141397053 / 1000000000000000 : ℝ) (1389228860973
    / 1000000000000 : ℝ) (370477218907367 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell989_denomLower :
    (365383756123393 / 10000000000 : ℝ) ≤ Real.exp (13132647967387889 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (13132647967387889 / 1250000000000000 : ℝ) (694313992957
    / 500000000000 : ℝ) (365383756123393 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell989_product_lower :
    (13519366717387889 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (989 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell989_leftExp
    (by norm_num : (0 : ℝ) ≤ (34426791811 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell989_product_upper :
    Real.pi * Real.exp (99 / 80 : ℝ) ≤ (10829024641397053 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell989_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell989_endpointLower :
    (108780407 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (989 / 1600 : ℝ) (99 / 160 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13519366717387889 / 1250000000000000 : ℝ) (Real.pi * Real.exp (989 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell989_product_lower
  have hD : Real.exp (Real.pi * Real.exp (99 / 80 : ℝ) - (989 / 3200 : ℝ)) ≤
      (370477218907367 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell989_denomUpper
    linarith [hpThetaJensenCell989_product_upper]
  have hi : (1 / (370477218907367 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (99 / 80 : ℝ) - (989 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (370477218907367 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (370477218907367 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((989 / 3200 : ℝ) - Real.pi * Real.exp (99 / 80 : ℝ)) := by
    rw [show (989 / 3200 : ℝ) - Real.pi * Real.exp (99 / 80 : ℝ) =
      -(Real.pi * Real.exp (99 / 80 : ℝ) - (989 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (989 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (989 / 800 : ℝ)) := by
    have h := hpThetaJensenCell989_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (370477218907367 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell989_endpointUpper :
    hpThetaJensenKernelEndpointUpper (989 / 1600 : ℝ) (99 / 160 : ℝ) ≤ (110886471 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (99 / 80 : ℝ)) (10829024641397053 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (99 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell989_product_upper
  have hD : (365383756123393 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (989 / 800 : ℝ) - (99 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell989_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell989_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (989 / 800 : ℝ) - (99 / 320 : ℝ)) ≤
      (1 / (365383756123393 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (365383756123393 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((99 / 320 : ℝ) - Real.pi * Real.exp (989 / 800 : ℝ)) ≤
      (2 / (365383756123393 / 10000000000 : ℝ) : ℝ) := by
    rw [show (99 / 320 : ℝ) - Real.pi * Real.exp (989 / 800 : ℝ) =
      -(Real.pi * Real.exp (989 / 800 : ℝ) - (99 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (10829024641397053 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (10829024641397053 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell989_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (989 / 1600 : ℝ) (99 / 160 : ℝ)) :
    (108780407 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (110886471 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell989_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell989_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell990_leftExp :
    (2154365763 / 625000000 : ℝ) ≤ Real.exp (99 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (99 / 80 : ℝ) (16241083827 / 15625000000 : ℝ) (2154365763
    / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell990_rightExp :
    Real.exp (991 / 800 : ℝ) ≤ (17256483233 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (991 / 800 : ℝ) (1039469968431 / 1000000000000 : ℝ)
    (17256483233 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell990_denomUpper :
    Real.exp (52665971929410169 / 5000000000000000 : ℝ) ≤ (93853010358519 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (52665971929410169 / 5000000000000000 : ℝ) (1389803436509
    / 1000000000000 : ℝ) (93853010358519 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell990_denomLower :
    (370244466518053 / 10000000000 : ℝ) ≤ Real.exp (821822944826837 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (821822944826837 / 78125000000000 : ℝ) (1389201578191 /
    1000000000000 : ℝ) (370244466518053 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell990_product_lower :
    (846017280764337 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (99 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell990_leftExp
    (by norm_num : (0 : ℝ) ≤ (2154365763 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell990_product_upper :
    Real.pi * Real.exp (991 / 800 : ℝ) ≤ (54212846929410169 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell990_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell990_endpointLower :
    (107640839 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (99 / 160 : ℝ) (991 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (846017280764337 / 78125000000000 : ℝ) (Real.pi * Real.exp (99 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell990_product_lower
  have hD : Real.exp (Real.pi * Real.exp (991 / 800 : ℝ) - (99 / 320 : ℝ)) ≤
      (93853010358519 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell990_denomUpper
    linarith [hpThetaJensenCell990_product_upper]
  have hi : (1 / (93853010358519 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (991 / 800 : ℝ) - (99 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (93853010358519 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (93853010358519 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((99 / 320 : ℝ) - Real.pi * Real.exp (991 / 800 : ℝ)) := by
    rw [show (99 / 320 : ℝ) - Real.pi * Real.exp (991 / 800 : ℝ) =
      -(Real.pi * Real.exp (991 / 800 : ℝ) - (99 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (99 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (99 / 80 : ℝ)) := by
    have h := hpThetaJensenCell990_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (93853010358519 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell990_endpointUpper :
    hpThetaJensenKernelEndpointUpper (99 / 160 : ℝ) (991 / 1600 : ℝ) ≤ (219453331 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (991 / 800 : ℝ)) (54212846929410169 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (991 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell990_product_upper
  have hD : (370244466518053 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (99 / 80 : ℝ) - (991 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell990_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell990_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (99 / 80 : ℝ) - (991 / 3200 : ℝ)) ≤
      (1 / (370244466518053 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (370244466518053 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((991 / 3200 : ℝ) - Real.pi * Real.exp (99 / 80 : ℝ)) ≤
      (2 / (370244466518053 / 10000000000 : ℝ) : ℝ) := by
    rw [show (991 / 3200 : ℝ) - Real.pi * Real.exp (99 / 80 : ℝ) =
      -(Real.pi * Real.exp (99 / 80 : ℝ) - (991 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (54212846929410169 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (54212846929410169 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell990_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (99 / 160 : ℝ) (991 / 1600 : ℝ)) :
    (107640839 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (219453331 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell990_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell990_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell991_leftExp :
    (539265101 / 156250000 : ℝ) ≤ Real.exp (991 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (991 / 800 : ℝ) (103946996843 / 100000000000 : ℝ)
    (539265101 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell991_rightExp :
    Real.exp (31 / 25 : ℝ) ≤ (34556134649 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (31 / 25 : ℝ) (12993882169 / 12500000000 : ℝ)
    (34556134649 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell991_denomUpper :
    Real.exp (105464435720355857 / 10000000000000000 : ℝ) ≤ (95104760387083 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (105464435720355857 / 10000000000000000 : ℝ)
    (1390378985789 / 1000000000000 : ℝ) (95104760387083 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell991_denomLower :
    (375176187117201 / 10000000000 : ℝ) ≤ Real.exp (205714178397599 / 19531250000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (205714178397599 / 19531250000000 : ℝ) (277955228451 /
    200000000000 : ℝ) (375176187117201 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell991_product_lower :
    (211768865897599 / 19531250000000 : ℝ) ≤ Real.pi * Real.exp (991 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell991_leftExp
    (by norm_num : (0 : ℝ) ≤ (539265101 / 156250000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell991_product_upper :
    Real.pi * Real.exp (31 / 25 : ℝ) ≤ (108561310720355857 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell991_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell991_endpointLower :
    (53255687 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (991 / 1600 : ℝ) (31 / 50 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (211768865897599 / 19531250000000 : ℝ) (Real.pi * Real.exp (991 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell991_product_lower
  have hD : Real.exp (Real.pi * Real.exp (31 / 25 : ℝ) - (991 / 3200 : ℝ)) ≤
      (95104760387083 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell991_denomUpper
    linarith [hpThetaJensenCell991_product_upper]
  have hi : (1 / (95104760387083 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (31 / 25 : ℝ) - (991 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (95104760387083 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (95104760387083 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((991 / 3200 : ℝ) - Real.pi * Real.exp (31 / 25 : ℝ)) := by
    rw [show (991 / 3200 : ℝ) - Real.pi * Real.exp (31 / 25 : ℝ) =
      -(Real.pi * Real.exp (31 / 25 : ℝ) - (991 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (991 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (991 / 800 : ℝ)) := by
    have h := hpThetaJensenCell991_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (95104760387083 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell991_endpointUpper :
    hpThetaJensenKernelEndpointUpper (991 / 1600 : ℝ) (31 / 50 : ℝ) ≤ (54288561 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (31 / 25 : ℝ)) (108561310720355857 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (31 / 50 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell991_product_upper
  have hD : (375176187117201 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (991 / 800 : ℝ) - (31 / 100 : ℝ)) := by
    apply le_trans hpThetaJensenCell991_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell991_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (991 / 800 : ℝ) - (31 / 100 : ℝ)) ≤
      (1 / (375176187117201 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (375176187117201 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((31 / 100 : ℝ) - Real.pi * Real.exp (991 / 800 : ℝ)) ≤
      (2 / (375176187117201 / 10000000000 : ℝ) : ℝ) := by
    rw [show (31 / 100 : ℝ) - Real.pi * Real.exp (991 / 800 : ℝ) =
      -(Real.pi * Real.exp (991 / 800 : ℝ) - (31 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (108561310720355857 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (108561310720355857 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell991_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (991 / 1600 : ℝ) (31 / 50 : ℝ)) :
    (53255687 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (54288561 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell991_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell991_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell992_leftExp :
    (34556134647 / 10000000000 : ℝ) ≤ Real.exp (31 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (31 / 25 : ℝ) (1039510573519 / 1000000000000 : ℝ)
    (34556134647 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell992_rightExp :
    Real.exp (993 / 800 : ℝ) ≤ (1383974273 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (993 / 800 : ℝ) (207910236039 / 200000000000 : ℝ)
    (1383974273 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell992_denomUpper :
    Real.exp (4223883888236889 / 400000000000000 : ℝ) ≤ (385499360695451 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4223883888236889 / 400000000000000 : ℝ) (173869438841 /
    125000000000 : ℝ) (385499360695451 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell992_denomLower :
    (380180039926173 / 10000000000 : ℝ) ≤ Real.exp (13182268894742253 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (13182268894742253 / 1250000000000000 : ℝ) (278070336009
    / 200000000000 : ℝ) (380180039926173 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell992_product_lower :
    (13570159519742253 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (31 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell992_leftExp
    (by norm_num : (0 : ℝ) ≤ (34556134647 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell992_product_upper :
    Real.pi * Real.exp (993 / 800 : ℝ) ≤ (4347883888236889 / 400000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell992_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell992_endpointLower :
    (210783883 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (31 / 50 : ℝ) (993 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13570159519742253 / 1250000000000000 : ℝ) (Real.pi * Real.exp (31 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell992_product_lower
  have hD : Real.exp (Real.pi * Real.exp (993 / 800 : ℝ) - (31 / 100 : ℝ)) ≤
      (385499360695451 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell992_denomUpper
    linarith [hpThetaJensenCell992_product_upper]
  have hi : (1 / (385499360695451 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (993 / 800 : ℝ) - (31 / 100 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (385499360695451 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (385499360695451 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((31 / 100 : ℝ) - Real.pi * Real.exp (993 / 800 : ℝ)) := by
    rw [show (31 / 100 : ℝ) - Real.pi * Real.exp (993 / 800 : ℝ) =
      -(Real.pi * Real.exp (993 / 800 : ℝ) - (31 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (31 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (31 / 25 : ℝ)) := by
    have h := hpThetaJensenCell992_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (385499360695451 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell992_endpointUpper :
    hpThetaJensenKernelEndpointUpper (31 / 50 : ℝ) (993 / 1600 : ℝ) ≤ (10743777 / 500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (993 / 800 : ℝ)) (4347883888236889 / 400000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (993 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell992_product_upper
  have hD : (380180039926173 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (31 / 25 : ℝ) - (993 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell992_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell992_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (31 / 25 : ℝ) - (993 / 3200 : ℝ)) ≤
      (1 / (380180039926173 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (380180039926173 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((993 / 3200 : ℝ) - Real.pi * Real.exp (31 / 25 : ℝ)) ≤
      (2 / (380180039926173 / 10000000000 : ℝ) : ℝ) := by
    rw [show (993 / 3200 : ℝ) - Real.pi * Real.exp (31 / 25 : ℝ) =
      -(Real.pi * Real.exp (31 / 25 : ℝ) - (993 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4347883888236889 / 400000000000000 : ℝ) ^ 2 - 6 *
      (4347883888236889 / 400000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell992_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (31 / 50 : ℝ) (993 / 1600 : ℝ)) :
    (210783883 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (10743777 / 500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell992_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell992_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell993_leftExp :
    (34599356823 / 10000000000 : ℝ) ≤ Real.exp (993 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (993 / 800 : ℝ) (519775590097 / 500000000000 : ℝ)
    (34599356823 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell993_rightExp :
    Real.exp (497 / 400 : ℝ) ≤ (34642633063 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (497 / 400 : ℝ) (129948973557 / 125000000000 : ℝ)
    (34642633063 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell993_denomUpper :
    Real.exp (105729928532289359 / 10000000000000000 : ℝ) ≤ (15626166399267 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (105729928532289359 / 10000000000000000 : ℝ)
    (347883253321 / 250000000000 : ℝ) (15626166399267 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell993_denomLower :
    (385257165646403 / 10000000000 : ℝ) ≤ Real.exp (13198851575035277 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (13198851575035277 / 1250000000000000 : ℝ) (1390928193473
    / 1000000000000 : ℝ) (385257165646403 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell993_product_lower :
    (13587132825035277 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (993 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell993_leftExp
    (by norm_num : (0 : ℝ) ≤ (34599356823 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell993_product_upper :
    Real.pi * Real.exp (497 / 400 : ℝ) ≤ (108833053532289359 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell993_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell993_endpointLower :
    (104282473 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (993 / 1600 : ℝ) (497 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13587132825035277 / 1250000000000000 : ℝ) (Real.pi * Real.exp (993 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell993_product_lower
  have hD : Real.exp (Real.pi * Real.exp (497 / 400 : ℝ) - (993 / 3200 : ℝ)) ≤
      (15626166399267 / 400000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell993_denomUpper
    linarith [hpThetaJensenCell993_product_upper]
  have hi : (1 / (15626166399267 / 400000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (497 / 400 : ℝ) - (993 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (15626166399267 / 400000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (15626166399267 / 400000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((993 / 3200 : ℝ) - Real.pi * Real.exp (497 / 400 : ℝ)) := by
    rw [show (993 / 3200 : ℝ) - Real.pi * Real.exp (497 / 400 : ℝ) =
      -(Real.pi * Real.exp (497 / 400 : ℝ) - (993 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (993 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (993 / 800 : ℝ)) := by
    have h := hpThetaJensenCell993_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (15626166399267 / 400000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell993_endpointUpper :
    hpThetaJensenKernelEndpointUpper (993 / 1600 : ℝ) (497 / 800 : ℝ) ≤ (5315427 / 250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (497 / 400 : ℝ)) (108833053532289359 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (497 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell993_product_upper
  have hD : (385257165646403 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (993 / 800 : ℝ) - (497 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell993_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell993_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (993 / 800 : ℝ) - (497 / 1600 : ℝ)) ≤
      (1 / (385257165646403 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (385257165646403 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((497 / 1600 : ℝ) - Real.pi * Real.exp (993 / 800 : ℝ)) ≤
      (2 / (385257165646403 / 10000000000 : ℝ) : ℝ) := by
    rw [show (497 / 1600 : ℝ) - Real.pi * Real.exp (993 / 800 : ℝ) =
      -(Real.pi * Real.exp (993 / 800 : ℝ) - (497 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (108833053532289359 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (108833053532289359 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell993_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (993 / 1600 : ℝ) (497 / 800 : ℝ)) :
    (104282473 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5315427 / 250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell993_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell993_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell994_leftExp :
    (34642633061 / 10000000000 : ℝ) ≤ Real.exp (497 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (497 / 400 : ℝ) (207918357691 / 200000000000 : ℝ)
    (34642633061 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell994_rightExp :
    Real.exp (199 / 160 : ℝ) ≤ (3468596343 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (199 / 160 : ℝ) (1039632398303 / 1000000000000 : ℝ)
    (3468596343 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell994_denomUpper :
    Real.exp (10586292990994399 / 1000000000000000 : ℝ) ≤ (395884619942921 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (10586292990994399 / 1000000000000000 : ℝ) (43503484231 /
    31250000000 : ℝ) (395884619942921 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell994_denomLower :
    (195204362340203 / 5000000000 : ℝ) ≤ Real.exp (13215455485421639 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (13215455485421639 / 1250000000000000 : ℝ) (2783011369 /
    2000000000 : ℝ) (195204362340203 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell994_product_lower :
    (13604127360421639 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (497 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell994_leftExp
    (by norm_num : (0 : ℝ) ≤ (34642633061 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell994_product_upper :
    Real.pi * Real.exp (199 / 160 : ℝ) ≤ (10896917990994399 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell994_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell994_endpointLower :
    (103182899 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (497 / 800 : ℝ) (199 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13604127360421639 / 1250000000000000 : ℝ) (Real.pi * Real.exp (497 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell994_product_lower
  have hD : Real.exp (Real.pi * Real.exp (199 / 160 : ℝ) - (497 / 1600 : ℝ)) ≤
      (395884619942921 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell994_denomUpper
    linarith [hpThetaJensenCell994_product_upper]
  have hi : (1 / (395884619942921 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (199 / 160 : ℝ) - (497 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (395884619942921 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (395884619942921 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((497 / 1600 : ℝ) - Real.pi * Real.exp (199 / 160 : ℝ)) := by
    rw [show (497 / 1600 : ℝ) - Real.pi * Real.exp (199 / 160 : ℝ) =
      -(Real.pi * Real.exp (199 / 160 : ℝ) - (497 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (497 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (497 / 400 : ℝ)) := by
    have h := hpThetaJensenCell994_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (395884619942921 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell994_endpointUpper :
    hpThetaJensenKernelEndpointUpper (497 / 800 : ℝ) (199 / 320 : ℝ) ≤ (52594681 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (199 / 160 : ℝ)) (10896917990994399 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (199 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell994_product_upper
  have hD : (195204362340203 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (497 / 400 : ℝ) - (199 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell994_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell994_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (497 / 400 : ℝ) - (199 / 640 : ℝ)) ≤
      (1 / (195204362340203 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (195204362340203 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((199 / 640 : ℝ) - Real.pi * Real.exp (497 / 400 : ℝ)) ≤
      (2 / (195204362340203 / 5000000000 : ℝ) : ℝ) := by
    rw [show (199 / 640 : ℝ) - Real.pi * Real.exp (497 / 400 : ℝ) =
      -(Real.pi * Real.exp (497 / 400 : ℝ) - (199 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (10896917990994399 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (10896917990994399 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell994_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (497 / 800 : ℝ) (199 / 320 : ℝ)) :
    (103182899 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (52594681 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell994_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell994_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell995_leftExp :
    (8671490857 / 2500000000 : ℝ) ≤ Real.exp (199 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (199 / 160 : ℝ) (519816199151 / 500000000000 : ℝ)
    (8671490857 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell995_rightExp :
    Real.exp (249 / 200 : ℝ) ≤ (17364673997 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (249 / 200 : ℝ) (1039673009737 / 1000000000000 : ℝ)
    (17364673997 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell995_denomUpper :
    Real.exp (52998050776257221 / 5000000000000000 : ℝ) ≤ (200595970625709 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (52998050776257221 / 5000000000000000 : ℝ) (348172739751
    / 250000000000 : ℝ) (200595970625709 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell995_denomLower :
    (98908974198743 / 2500000000 : ℝ) ≤ Real.exp (3308020163053043 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3308020163053043 / 312500000000000 : ℝ) (696042077529 /
    500000000000 : ℝ) (98908974198743 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell995_product_lower :
    (3405285788053043 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (199 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell995_leftExp
    (by norm_num : (0 : ℝ) ≤ (8671490857 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell995_product_upper :
    Real.pi * Real.exp (249 / 200 : ℝ) ≤ (54552738276257221 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell995_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell995_endpointLower :
    (204186303 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (199 / 320 : ℝ) (249 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3405285788053043 / 312500000000000 : ℝ) (Real.pi * Real.exp (199 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell995_product_lower
  have hD : Real.exp (Real.pi * Real.exp (249 / 200 : ℝ) - (199 / 640 : ℝ)) ≤
      (200595970625709 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell995_denomUpper
    linarith [hpThetaJensenCell995_product_upper]
  have hi : (1 / (200595970625709 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (249 / 200 : ℝ) - (199 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (200595970625709 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (200595970625709 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((199 / 640 : ℝ) - Real.pi * Real.exp (249 / 200 : ℝ)) := by
    rw [show (199 / 640 : ℝ) - Real.pi * Real.exp (249 / 200 : ℝ) =
      -(Real.pi * Real.exp (249 / 200 : ℝ) - (199 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (199 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (199 / 160 : ℝ)) := by
    have h := hpThetaJensenCell995_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (200595970625709 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell995_endpointUpper :
    hpThetaJensenKernelEndpointUpper (199 / 320 : ℝ) (249 / 400 : ℝ) ≤ (52040083 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (249 / 200 : ℝ)) (54552738276257221 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (249 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell995_product_upper
  have hD : (98908974198743 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (199 / 160 : ℝ) - (249 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell995_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell995_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (199 / 160 : ℝ) - (249 / 800 : ℝ)) ≤
      (1 / (98908974198743 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (98908974198743 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((249 / 800 : ℝ) - Real.pi * Real.exp (199 / 160 : ℝ)) ≤
      (2 / (98908974198743 / 2500000000 : ℝ) : ℝ) := by
    rw [show (249 / 800 : ℝ) - Real.pi * Real.exp (199 / 160 : ℝ) =
      -(Real.pi * Real.exp (199 / 160 : ℝ) - (249 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (54552738276257221 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (54552738276257221 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell995_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (199 / 320 : ℝ) (249 / 400 : ℝ)) :
    (204186303 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (52040083 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell995_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell995_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell996_leftExp :
    (4341168499 / 1250000000 : ℝ) ≤ Real.exp (249 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (249 / 200 : ℝ) (129959126217 / 125000000000 : ℝ)
    (4341168499 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell996_rightExp :
    Real.exp (997 / 800 : ℝ) ≤ (34772786823 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (997 / 800 : ℝ) (1039713622757 / 1000000000000 : ℝ)
    (34772786823 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell996_denomUpper :
    Real.exp (106129443673629039 / 10000000000000000 : ℝ) ≤ (203288672476431 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (106129443673629039 / 10000000000000000 : ℝ) (55730856243
    / 40000000000 : ℝ) (203288672476431 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell996_denomLower :
    (400939881925211 / 10000000000 : ℝ) ≤ Real.exp (1656090887763801 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1656090887763801 / 156250000000000 : ℝ) (1392663607101 /
    1000000000000 : ℝ) (400939881925211 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell996_product_lower :
    (1704772528388801 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (249 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell996_leftExp
    (by norm_num : (0 : ℝ) ≤ (4341168499 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell996_product_upper :
    Real.pi * Real.exp (997 / 800 : ℝ) ≤ (109241943673629039 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell996_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell996_endpointLower :
    (50506581 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (249 / 400 : ℝ) (997 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1704772528388801 / 156250000000000 : ℝ) (Real.pi * Real.exp (249 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell996_product_lower
  have hD : Real.exp (Real.pi * Real.exp (997 / 800 : ℝ) - (249 / 800 : ℝ)) ≤
      (203288672476431 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell996_denomUpper
    linarith [hpThetaJensenCell996_product_upper]
  have hi : (1 / (203288672476431 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (997 / 800 : ℝ) - (249 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (203288672476431 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (203288672476431 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((249 / 800 : ℝ) - Real.pi * Real.exp (997 / 800 : ℝ)) := by
    rw [show (249 / 800 : ℝ) - Real.pi * Real.exp (997 / 800 : ℝ) =
      -(Real.pi * Real.exp (997 / 800 : ℝ) - (249 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (249 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (249 / 200 : ℝ)) := by
    have h := hpThetaJensenCell996_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (203288672476431 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell996_endpointUpper :
    hpThetaJensenKernelEndpointUpper (249 / 400 : ℝ) (997 / 1600 : ℝ) ≤ (102980883 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (997 / 800 : ℝ)) (109241943673629039 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (997 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell996_product_upper
  have hD : (400939881925211 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (249 / 200 : ℝ) - (997 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell996_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell996_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (249 / 200 : ℝ) - (997 / 3200 : ℝ)) ≤
      (1 / (400939881925211 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (400939881925211 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((997 / 3200 : ℝ) - Real.pi * Real.exp (249 / 200 : ℝ)) ≤
      (2 / (400939881925211 / 10000000000 : ℝ) : ℝ) := by
    rw [show (997 / 3200 : ℝ) - Real.pi * Real.exp (249 / 200 : ℝ) =
      -(Real.pi * Real.exp (249 / 200 : ℝ) - (997 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (109241943673629039 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (109241943673629039 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell996_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (249 / 400 : ℝ) (997 / 1600 : ℝ)) :
    (50506581 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (102980883 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell996_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell996_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell997_leftExp :
    (34772786821 / 10000000000 : ℝ) ≤ Real.exp (997 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (997 / 800 : ℝ) (259928405689 / 250000000000 : ℝ)
    (34772786821 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell997_rightExp :
    Real.exp (499 / 400 : ℝ) ≤ (2176017499 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (499 / 400 : ℝ) (259938559341 / 250000000000 : ℝ)
    (2176017499 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell997_denomUpper :
    Real.exp (6641434780235907 / 625000000000000 : ℝ) ≤ (412042072728917 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (6641434780235907 / 625000000000000 : ℝ) (174231604819 /
    125000000000 : ℝ) (412042072728917 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell997_denomLower :
    (406321900349177 / 10000000000 : ℝ) ≤ Real.exp (13265394861819879 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (13265394861819879 / 1250000000000000 : ℝ) (174155505323
    / 125000000000 : ℝ) (406321900349177 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell997_product_lower :
    (13655238611819879 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (997 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell997_leftExp
    (by norm_num : (0 : ℝ) ≤ (34772786821 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell997_product_upper :
    Real.pi * Real.exp (499 / 400 : ℝ) ≤ (6836161342735907 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell997_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell997_endpointLower :
    (49971431 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (997 / 1600 : ℝ) (499 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13655238611819879 / 1250000000000000 : ℝ) (Real.pi * Real.exp (997 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell997_product_lower
  have hD : Real.exp (Real.pi * Real.exp (499 / 400 : ℝ) - (997 / 3200 : ℝ)) ≤
      (412042072728917 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell997_denomUpper
    linarith [hpThetaJensenCell997_product_upper]
  have hi : (1 / (412042072728917 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (499 / 400 : ℝ) - (997 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (412042072728917 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (412042072728917 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((997 / 3200 : ℝ) - Real.pi * Real.exp (499 / 400 : ℝ)) := by
    rw [show (997 / 3200 : ℝ) - Real.pi * Real.exp (499 / 400 : ℝ) =
      -(Real.pi * Real.exp (499 / 400 : ℝ) - (997 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (997 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (997 / 800 : ℝ)) := by
    have h := hpThetaJensenCell997_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (412042072728917 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell997_endpointUpper :
    hpThetaJensenKernelEndpointUpper (997 / 1600 : ℝ) (499 / 800 : ℝ) ≤ (25472861 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (499 / 400 : ℝ)) (6836161342735907 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (499 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell997_product_upper
  have hD : (406321900349177 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (997 / 800 : ℝ) - (499 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell997_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell997_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (997 / 800 : ℝ) - (499 / 1600 : ℝ)) ≤
      (1 / (406321900349177 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (406321900349177 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((499 / 1600 : ℝ) - Real.pi * Real.exp (997 / 800 : ℝ)) ≤
      (2 / (406321900349177 / 10000000000 : ℝ) : ℝ) := by
    rw [show (499 / 1600 : ℝ) - Real.pi * Real.exp (997 / 800 : ℝ) =
      -(Real.pi * Real.exp (997 / 800 : ℝ) - (499 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (6836161342735907 / 625000000000000 : ℝ) ^ 2 - 6 *
      (6836161342735907 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell997_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (997 / 1600 : ℝ) (499 / 800 : ℝ)) :
    (49971431 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (25472861 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell997_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell997_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell998_leftExp :
    (17408139991 / 5000000000 : ℝ) ≤ Real.exp (499 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (499 / 400 : ℝ) (1039754237363 / 1000000000000 : ℝ)
    (17408139991 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell998_rightExp :
    Real.exp (999 / 800 : ℝ) ≤ (17429913773 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (999 / 800 : ℝ) (1039794853557 / 1000000000000 : ℝ)
    (17429913773 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell998_denomUpper :
    Real.exp (53198320099860389 / 5000000000000000 : ℝ) ≤ (417587387599331 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (53198320099860389 / 5000000000000000 : ℝ) (1394435258409
    / 1000000000000 : ℝ) (417587387599331 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell998_denomLower :
    (205891596469783 / 5000000000 : ℝ) ≤ Real.exp (6641041978825709 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6641041978825709 / 625000000000000 : ℝ) (1393825463451 /
    1000000000000 : ℝ) (205891596469783 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell998_product_lower :
    (6836159166325709 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (499 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell998_leftExp
    (by norm_num : (0 : ℝ) ≤ (17408139991 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell998_product_upper :
    Real.pi * Real.exp (999 / 800 : ℝ) ≤ (54757695099860389 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell998_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell998_endpointLower :
    (12360273 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (499 / 800 : ℝ) (999 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6836159166325709 / 625000000000000 : ℝ) (Real.pi * Real.exp (499 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell998_product_lower
  have hD : Real.exp (Real.pi * Real.exp (999 / 800 : ℝ) - (499 / 1600 : ℝ)) ≤
      (417587387599331 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell998_denomUpper
    linarith [hpThetaJensenCell998_product_upper]
  have hi : (1 / (417587387599331 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (999 / 800 : ℝ) - (499 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (417587387599331 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (417587387599331 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((499 / 1600 : ℝ) - Real.pi * Real.exp (999 / 800 : ℝ)) := by
    rw [show (499 / 1600 : ℝ) - Real.pi * Real.exp (999 / 800 : ℝ) =
      -(Real.pi * Real.exp (999 / 800 : ℝ) - (499 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (499 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (499 / 400 : ℝ)) := by
    have h := hpThetaJensenCell998_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (417587387599331 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell998_endpointUpper :
    hpThetaJensenKernelEndpointUpper (499 / 800 : ℝ) (999 / 1600 : ℝ) ≤ (201623561 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (999 / 800 : ℝ)) (54757695099860389 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (999 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell998_product_upper
  have hD : (205891596469783 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (499 / 400 : ℝ) - (999 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell998_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell998_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (499 / 400 : ℝ) - (999 / 3200 : ℝ)) ≤
      (1 / (205891596469783 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (205891596469783 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((999 / 3200 : ℝ) - Real.pi * Real.exp (499 / 400 : ℝ)) ≤
      (2 / (205891596469783 / 5000000000 : ℝ) : ℝ) := by
    rw [show (999 / 3200 : ℝ) - Real.pi * Real.exp (499 / 400 : ℝ) =
      -(Real.pi * Real.exp (499 / 400 : ℝ) - (999 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (54757695099860389 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (54757695099860389 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell998_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (499 / 800 : ℝ) (999 / 1600 : ℝ)) :
    (12360273 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (201623561 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell998_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell998_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell999_leftExp :
    (4357478443 / 1250000000 : ℝ) ≤ Real.exp (999 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (999 / 800 : ℝ) (259948713389 / 250000000000 : ℝ)
    (4357478443 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell999_rightExp :
    Real.exp (5 / 4 : ℝ) ≤ (4362928697 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (5 / 4 : ℝ) (1039835471337 / 1000000000000 : ℝ)
    (4362928697 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell999_denomUpper :
    Real.exp (13316311878994321 / 1250000000000000 : ℝ) ≤ (8464291477027 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (13316311878994321 / 1250000000000000 : ℝ) (1395018667599
    / 1000000000000 : ℝ) (8464291477027 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell999_denomLower :
    (417325021959319 / 10000000000 : ℝ) ≤ Real.exp (1662349302087657 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1662349302087657 / 156250000000000 : ℝ) (4357524599 /
    3125000000 : ℝ) (417325021959319 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell999_product_lower :
    (1711177427087657 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (999 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell999_leftExp
    (by norm_num : (0 : ℝ) ≤ (4357478443 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell999_product_upper :
    Real.pi * Real.exp (5 / 4 : ℝ) ≤ (13706546253994321 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell999_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell999_endpointLower :
    (97831061 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (999 / 1600 : ℝ) (5 / 8 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1711177427087657 / 156250000000000 : ℝ) (Real.pi * Real.exp (999 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell999_product_lower
  have hD : Real.exp (Real.pi * Real.exp (5 / 4 : ℝ) - (999 / 3200 : ℝ)) ≤
      (8464291477027 / 200000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell999_denomUpper
    linarith [hpThetaJensenCell999_product_upper]
  have hi : (1 / (8464291477027 / 200000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (5 / 4 : ℝ) - (999 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (8464291477027 / 200000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (8464291477027 / 200000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((999 / 3200 : ℝ) - Real.pi * Real.exp (5 / 4 : ℝ)) := by
    rw [show (999 / 3200 : ℝ) - Real.pi * Real.exp (5 / 4 : ℝ) =
      -(Real.pi * Real.exp (5 / 4 : ℝ) - (999 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (999 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (999 / 800 : ℝ)) := by
    have h := hpThetaJensenCell999_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (8464291477027 / 200000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell999_endpointUpper :
    hpThetaJensenKernelEndpointUpper (999 / 1600 : ℝ) (5 / 8 : ℝ) ≤ (779233 / 39062500 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (5 / 4 : ℝ)) (13706546253994321 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (5 / 8 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell999_product_upper
  have hD : (417325021959319 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (999 / 800 : ℝ) - (5 / 16 : ℝ)) := by
    apply le_trans hpThetaJensenCell999_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell999_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (999 / 800 : ℝ) - (5 / 16 : ℝ)) ≤
      (1 / (417325021959319 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (417325021959319 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((5 / 16 : ℝ) - Real.pi * Real.exp (999 / 800 : ℝ)) ≤
      (2 / (417325021959319 / 10000000000 : ℝ) : ℝ) := by
    rw [show (5 / 16 : ℝ) - Real.pi * Real.exp (999 / 800 : ℝ) =
      -(Real.pi * Real.exp (999 / 800 : ℝ) - (5 / 16 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (13706546253994321 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (13706546253994321 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell999_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (999 / 1600 : ℝ) (5 / 8 : ℝ)) :
    (97831061 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (779233 / 39062500 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell999_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell999_endpointUpper

def hpThetaJensenCellsBatch049Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (239005447 / 10000000000 : ℝ)
  | 1 => (378461 / 16000000 : ℝ)
  | 2 => (58523071 / 2500000000 : ℝ)
  | 3 => (115833889 / 5000000000 : ℝ)
  | 4 => (45852893 / 2000000000 : ℝ)
  | 5 => (113441101 / 5000000000 : ℝ)
  | 6 => (224520847 / 10000000000 : ℝ)
  | 7 => (111090129 / 5000000000 : ℝ)
  | 8 => (109930147 / 5000000000 : ℝ)
  | 9 => (108780407 / 5000000000 : ℝ)
  | 10 => (107640839 / 5000000000 : ℝ)
  | 11 => (53255687 / 2500000000 : ℝ)
  | 12 => (210783883 / 10000000000 : ℝ)
  | 13 => (104282473 / 5000000000 : ℝ)
  | 14 => (103182899 / 5000000000 : ℝ)
  | 15 => (204186303 / 10000000000 : ℝ)
  | 16 => (50506581 / 2500000000 : ℝ)
  | 17 => (49971431 / 2500000000 : ℝ)
  | 18 => (12360273 / 625000000 : ℝ)
  | 19 => (97831061 / 5000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch049Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (121798263 / 5000000000 : ℝ)
  | 1 => (60271443 / 2500000000 : ℝ)
  | 2 => (47719367 / 2000000000 : ℝ)
  | 3 => (236129567 / 10000000000 : ℝ)
  | 4 => (14605239 / 625000000 : ℝ)
  | 5 => (115629731 / 5000000000 : ℝ)
  | 6 => (14303521 / 625000000 : ℝ)
  | 7 => (113237151 / 5000000000 : ℝ)
  | 8 => (112056609 / 5000000000 : ℝ)
  | 9 => (110886471 / 5000000000 : ℝ)
  | 10 => (219453331 / 10000000000 : ℝ)
  | 11 => (54288561 / 2500000000 : ℝ)
  | 12 => (10743777 / 500000000 : ℝ)
  | 13 => (5315427 / 250000000 : ℝ)
  | 14 => (52594681 / 2500000000 : ℝ)
  | 15 => (52040083 / 2500000000 : ℝ)
  | 16 => (102980883 / 5000000000 : ℝ)
  | 17 => (25472861 / 1250000000 : ℝ)
  | 18 => (201623561 / 10000000000 : ℝ)
  | 19 => (779233 / 39062500 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch049_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((980 : ℝ) + (j.val : ℝ)) / 1600)
      (((980 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch049Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch049Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell980_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell981_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell982_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell983_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell984_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell985_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell986_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell987_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell988_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell989_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell990_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell991_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell992_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell993_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell994_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell995_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell996_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell997_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell998_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell999_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper] at h ⊢
    exact h

end HodgeProofHP
