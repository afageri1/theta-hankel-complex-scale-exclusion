import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell800_leftExp :
    (6795704571 / 2500000000 : ℝ) ≤ Real.exp (1 / 1 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1 / 1 : ℝ) (1031743407499 / 1000000000000 : ℝ)
    (6795704571 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell800_rightExp :
    Real.exp (801 / 800 : ℝ) ≤ (13608409027 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (801 / 800 : ℝ) (257945927691 / 250000000000 : ℝ)
    (13608409027 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell800_denomUpper :
    Real.exp (41502082540360011 / 5000000000000000 : ℝ) ≤ (40255487182353 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (41502082540360011 / 5000000000000000 : ℝ) (1296136628861
    / 1000000000000 : ℝ) (40255487182353 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell800_denomLower :
    (4976905031283 / 1250000000 : ℝ) ≤ Real.exp (2590443733077129 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2590443733077129 / 312500000000000 : ℝ) (1295691297661 /
    1000000000000 : ℝ) (4976905031283 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell800_product_lower :
    (2668666389327129 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (1 / 1 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell800_leftExp
    (by norm_num : (0 : ℝ) ≤ (6795704571 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell800_product_upper :
    Real.pi * Real.exp (801 / 800 : ℝ) ≤ (42752082540360011 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell800_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell800_endpointLower :
    (597358877 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 2 : ℝ) (801 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2668666389327129 / 312500000000000 : ℝ) (Real.pi * Real.exp (1 / 1 : ℝ))
    (by norm_num) hpThetaJensenCell800_product_lower
  have hD : Real.exp (Real.pi * Real.exp (801 / 800 : ℝ) - (1 / 4 : ℝ)) ≤
      (40255487182353 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell800_denomUpper
    linarith [hpThetaJensenCell800_product_upper]
  have hi : (1 / (40255487182353 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (801 / 800 : ℝ) - (1 / 4 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (40255487182353 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (40255487182353 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1 / 4 : ℝ) - Real.pi * Real.exp (801 / 800 : ℝ)) := by
    rw [show (1 / 4 : ℝ) - Real.pi * Real.exp (801 / 800 : ℝ) =
      -(Real.pi * Real.exp (801 / 800 : ℝ) - (1 / 4 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1 / 1 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1 / 1 : ℝ)) := by
    have h := hpThetaJensenCell800_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (40255487182353 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell800_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1 / 2 : ℝ) (801 / 1600 : ℝ) ≤ (75904047 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (801 / 800 : ℝ)) (42752082540360011 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (801 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell800_product_upper
  have hD : (4976905031283 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1 / 1 : ℝ) - (801 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell800_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell800_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1 / 1 : ℝ) - (801 / 3200 : ℝ)) ≤
      (1 / (4976905031283 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4976905031283 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((801 / 3200 : ℝ) - Real.pi * Real.exp (1 / 1 : ℝ)) ≤
      (2 / (4976905031283 / 1250000000 : ℝ) : ℝ) := by
    rw [show (801 / 3200 : ℝ) - Real.pi * Real.exp (1 / 1 : ℝ) =
      -(Real.pi * Real.exp (1 / 1 : ℝ) - (801 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (42752082540360011 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (42752082540360011 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell800_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1 / 2 : ℝ) (801 / 1600 : ℝ)) :
    (597358877 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (75904047 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell800_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell800_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell801_leftExp :
    (6804204513 / 2500000000 : ℝ) ≤ Real.exp (801 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (801 / 800 : ℝ) (1031783710763 / 1000000000000 : ℝ)
    (6804204513 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell801_rightExp :
    Real.exp (401 / 400 : ℝ) ≤ (6812715087 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (401 / 400 : ℝ) (515912007801 / 500000000000 : ℝ)
    (6812715087 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell801_denomUpper :
    Real.exp (20776996778313591 / 2500000000000000 : ℝ) ≤ (406756049329 / 100000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (20776996778313591 / 2500000000000000 : ℝ) (1296557220647
    / 1000000000000 : ℝ) (406756049329 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell801_denomLower :
    (4023022584367 / 1000000000 : ℝ) ≤ Real.exp (2593683995550587 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2593683995550587 / 312500000000000 : ℝ) (324027800919 /
    250000000000 : ℝ) (4023022584367 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell801_product_lower :
    (2672004308050587 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (801 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell801_leftExp
    (by norm_num : (0 : ℝ) ≤ (6804204513 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell801_product_upper :
    Real.pi * Real.exp (401 / 400 : ℝ) ≤ (21402778028313591 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell801_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell801_endpointLower :
    (592826637 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (801 / 1600 : ℝ) (401 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2672004308050587 / 312500000000000 : ℝ) (Real.pi * Real.exp (801 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell801_product_lower
  have hD : Real.exp (Real.pi * Real.exp (401 / 400 : ℝ) - (801 / 3200 : ℝ)) ≤
      (406756049329 / 100000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell801_denomUpper
    linarith [hpThetaJensenCell801_product_upper]
  have hi : (1 / (406756049329 / 100000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (401 / 400 : ℝ) - (801 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (406756049329 / 100000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (406756049329 / 100000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((801 / 3200 : ℝ) - Real.pi * Real.exp (401 / 400 : ℝ)) := by
    rw [show (801 / 3200 : ℝ) - Real.pi * Real.exp (401 / 400 : ℝ) =
      -(Real.pi * Real.exp (401 / 400 : ℝ) - (801 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (801 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (801 / 800 : ℝ)) := by
    have h := hpThetaJensenCell801_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (406756049329 / 100000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell801_endpointUpper :
    hpThetaJensenKernelEndpointUpper (801 / 1600 : ℝ) (401 / 800 : ℝ) ≤ (1205266069 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (401 / 400 : ℝ)) (21402778028313591 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (401 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell801_product_upper
  have hD : (4023022584367 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (801 / 800 : ℝ) - (401 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell801_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell801_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (801 / 800 : ℝ) - (401 / 1600 : ℝ)) ≤
      (1 / (4023022584367 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4023022584367 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((401 / 1600 : ℝ) - Real.pi * Real.exp (801 / 800 : ℝ)) ≤
      (2 / (4023022584367 / 1000000000 : ℝ) : ℝ) := by
    rw [show (401 / 1600 : ℝ) - Real.pi * Real.exp (801 / 800 : ℝ) =
      -(Real.pi * Real.exp (801 / 800 : ℝ) - (401 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (21402778028313591 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (21402778028313591 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell801_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (801 / 1600 : ℝ) (401 / 800 : ℝ)) :
    (592826637 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1205266069 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell801_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell801_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell802_leftExp :
    (13625430173 / 5000000000 : ℝ) ≤ Real.exp (401 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (401 / 400 : ℝ) (1031824015601 / 1000000000000 : ℝ)
    (13625430173 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell802_rightExp :
    Real.exp (803 / 800 : ℝ) ≤ (27284945223 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (803 / 800 : ℝ) (206372864403 / 200000000000 : ℝ)
    (27284945223 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell802_denomUpper :
    Real.exp (83211942917960239 / 10000000000000000 : ℝ) ≤ (41100656961119 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (83211942917960239 / 10000000000000000 : ℝ) (12969784911
    / 10000000000 : ℝ) (41100656961119 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell802_denomLower :
    (8130015964121 / 2000000000 : ℝ) ≤ Real.exp (5193856866006927 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5193856866006927 / 625000000000000 : ℝ) (1296531787073 /
    1000000000000 : ℝ) (8130015964121 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell802_product_lower :
    (5350692803506927 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (401 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell802_leftExp
    (by norm_num : (0 : ℝ) ≤ (13625430173 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell802_product_upper :
    Real.pi * Real.exp (803 / 800 : ℝ) ≤ (85718192917960239 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell802_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell802_endpointLower :
    (1176641353 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (401 / 800 : ℝ) (803 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5350692803506927 / 625000000000000 : ℝ) (Real.pi * Real.exp (401 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell802_product_lower
  have hD : Real.exp (Real.pi * Real.exp (803 / 800 : ℝ) - (401 / 1600 : ℝ)) ≤
      (41100656961119 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell802_denomUpper
    linarith [hpThetaJensenCell802_product_upper]
  have hi : (1 / (41100656961119 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (803 / 800 : ℝ) - (401 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (41100656961119 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (41100656961119 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((401 / 1600 : ℝ) - Real.pi * Real.exp (803 / 800 : ℝ)) := by
    rw [show (401 / 1600 : ℝ) - Real.pi * Real.exp (803 / 800 : ℝ) =
      -(Real.pi * Real.exp (803 / 800 : ℝ) - (401 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (401 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (401 / 400 : ℝ)) := by
    have h := hpThetaJensenCell802_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (41100656961119 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell802_endpointUpper :
    hpThetaJensenKernelEndpointUpper (401 / 800 : ℝ) (803 / 1600 : ℝ) ≤ (598060299 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (803 / 800 : ℝ)) (85718192917960239 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (803 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell802_product_upper
  have hD : (8130015964121 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (401 / 400 : ℝ) - (803 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell802_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell802_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (401 / 400 : ℝ) - (803 / 3200 : ℝ)) ≤
      (1 / (8130015964121 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (8130015964121 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((803 / 3200 : ℝ) - Real.pi * Real.exp (401 / 400 : ℝ)) ≤
      (2 / (8130015964121 / 2000000000 : ℝ) : ℝ) := by
    rw [show (803 / 3200 : ℝ) - Real.pi * Real.exp (401 / 400 : ℝ) =
      -(Real.pi * Real.exp (401 / 400 : ℝ) - (803 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (85718192917960239 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (85718192917960239 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell802_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (401 / 800 : ℝ) (803 / 1600 : ℝ)) :
    (1176641353 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (598060299 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell802_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell802_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell803_leftExp :
    (27284945221 / 10000000000 : ℝ) ≤ Real.exp (803 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (803 / 800 : ℝ) (515932161007 / 500000000000 : ℝ)
    (27284945221 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell803_rightExp :
    Real.exp (201 / 200 : ℝ) ≤ (27319072729 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (201 / 200 : ℝ) (515952315001 / 500000000000 : ℝ)
    (27319072729 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell803_denomUpper :
    Real.exp (83316032651917297 / 10000000000000000 : ℝ) ≤ (10382676728117 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (83316032651917297 / 10000000000000000 : ℝ)
    (1297400441429 / 1000000000000 : ℝ) (10382676728117 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell803_denomLower :
    (4107486497633 / 1000000000 : ℝ) ≤ Real.exp (10400708203341479 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10400708203341479 / 1250000000000000 : ℝ) (324238262281
    / 250000000000 : ℝ) (4107486497633 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell803_product_lower :
    (10714770703341479 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (803 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell803_leftExp
    (by norm_num : (0 : ℝ) ≤ (27284945221 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell803_product_upper :
    Real.pi * Real.exp (201 / 200 : ℝ) ≤ (85825407651917297 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell803_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell803_endpointLower :
    (58384091 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (803 / 1600 : ℝ) (201 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10714770703341479 / 1250000000000000 : ℝ) (Real.pi * Real.exp (803 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell803_product_lower
  have hD : Real.exp (Real.pi * Real.exp (201 / 200 : ℝ) - (803 / 3200 : ℝ)) ≤
      (10382676728117 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell803_denomUpper
    linarith [hpThetaJensenCell803_product_upper]
  have hi : (1 / (10382676728117 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (201 / 200 : ℝ) - (803 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (10382676728117 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (10382676728117 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((803 / 3200 : ℝ) - Real.pi * Real.exp (201 / 200 : ℝ)) := by
    rw [show (803 / 3200 : ℝ) - Real.pi * Real.exp (201 / 200 : ℝ) =
      -(Real.pi * Real.exp (201 / 200 : ℝ) - (803 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (803 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (803 / 800 : ℝ)) := by
    have h := hpThetaJensenCell803_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (10382676728117 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell803_endpointUpper :
    hpThetaJensenKernelEndpointUpper (803 / 1600 : ℝ) (201 / 400 : ℝ) ≤ (237405633 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (201 / 200 : ℝ)) (85825407651917297 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (201 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell803_product_upper
  have hD : (4107486497633 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (803 / 800 : ℝ) - (201 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell803_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell803_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (803 / 800 : ℝ) - (201 / 800 : ℝ)) ≤
      (1 / (4107486497633 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4107486497633 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((201 / 800 : ℝ) - Real.pi * Real.exp (803 / 800 : ℝ)) ≤
      (2 / (4107486497633 / 1000000000 : ℝ) : ℝ) := by
    rw [show (201 / 800 : ℝ) - Real.pi * Real.exp (803 / 800 : ℝ) =
      -(Real.pi * Real.exp (803 / 800 : ℝ) - (201 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (85825407651917297 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (85825407651917297 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell803_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (803 / 1600 : ℝ) (201 / 400 : ℝ)) :
    (58384091 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (237405633 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell803_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell803_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell804_leftExp :
    (27319072727 / 10000000000 : ℝ) ≤ Real.exp (201 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (201 / 200 : ℝ) (1031904630001 / 1000000000000 : ℝ)
    (27319072727 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell804_rightExp :
    Real.exp (161 / 160 : ℝ) ≤ (13676621461 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (161 / 160 : ℝ) (257986234891 / 250000000000 : ℝ)
    (13676621461 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell804_denomUpper :
    Real.exp (41710128245527373 / 5000000000000000 : ℝ) ≤ (20982909699913 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (41710128245527373 / 5000000000000000 : ℝ) (648911536461
    / 500000000000 : ℝ) (20982909699913 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell804_denomLower :
    (1660185796613 / 400000000 : ℝ) ≤ Real.exp (10413719415820173 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10413719415820173 / 1250000000000000 : ℝ) (1297374991037
    / 1000000000000 : ℝ) (1660185796613 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell804_product_lower :
    (10728172540820173 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (201 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell804_leftExp
    (by norm_num : (0 : ℝ) ≤ (27319072727 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell804_product_upper :
    Real.pi * Real.exp (161 / 160 : ℝ) ≤ (42966378245527373 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell804_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell804_endpointLower :
    (231754901 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (201 / 400 : ℝ) (161 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10728172540820173 / 1250000000000000 : ℝ) (Real.pi * Real.exp (201 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell804_product_lower
  have hD : Real.exp (Real.pi * Real.exp (161 / 160 : ℝ) - (201 / 800 : ℝ)) ≤
      (20982909699913 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell804_denomUpper
    linarith [hpThetaJensenCell804_product_upper]
  have hi : (1 / (20982909699913 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (161 / 160 : ℝ) - (201 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (20982909699913 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (20982909699913 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((201 / 800 : ℝ) - Real.pi * Real.exp (161 / 160 : ℝ)) := by
    rw [show (201 / 800 : ℝ) - Real.pi * Real.exp (161 / 160 : ℝ) =
      -(Real.pi * Real.exp (161 / 160 : ℝ) - (201 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (201 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (201 / 200 : ℝ)) := by
    have h := hpThetaJensenCell804_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (20982909699913 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell804_endpointUpper :
    hpThetaJensenKernelEndpointUpper (201 / 400 : ℝ) (161 / 320 : ℝ) ≤ (1177988601 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (161 / 160 : ℝ)) (42966378245527373 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (161 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell804_product_upper
  have hD : (1660185796613 / 400000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (201 / 200 : ℝ) - (161 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell804_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell804_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (201 / 200 : ℝ) - (161 / 640 : ℝ)) ≤
      (1 / (1660185796613 / 400000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1660185796613 / 400000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((161 / 640 : ℝ) - Real.pi * Real.exp (201 / 200 : ℝ)) ≤
      (2 / (1660185796613 / 400000000 : ℝ) : ℝ) := by
    rw [show (161 / 640 : ℝ) - Real.pi * Real.exp (201 / 200 : ℝ) =
      -(Real.pi * Real.exp (201 / 200 : ℝ) - (161 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (42966378245527373 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (42966378245527373 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell804_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (201 / 400 : ℝ) (161 / 320 : ℝ)) :
    (231754901 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1177988601 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell804_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell804_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell805_leftExp :
    (683831073 / 250000000 : ℝ) ≤ Real.exp (161 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (161 / 160 : ℝ) (1031944939563 / 1000000000000 : ℝ)
    (683831073 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell805_rightExp :
    Real.exp (403 / 400 : ℝ) ≤ (5477491171 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (403 / 400 : ℝ) (1031985250701 / 1000000000000 : ℝ)
    (5477491171 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell805_denomUpper :
    Real.exp (16704922920375403 / 2000000000000000 : ℝ) ≤ (2120302995029 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (16704922920375403 / 2000000000000000 : ℝ) (1298246386831
    / 1000000000000 : ℝ) (2120302995029 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell805_denomLower :
    (41939484211947 / 10000000000 : ℝ) ≤ Real.exp (260668684786027 / 31250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (260668684786027 / 31250000000000 : ℝ) (648898807051 /
    500000000000 : ℝ) (41939484211947 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell805_product_lower :
    (268539778536027 / 31250000000000 : ℝ) ≤ Real.pi * Real.exp (161 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell805_leftExp
    (by norm_num : (0 : ℝ) ≤ (683831073 / 250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell805_product_upper :
    Real.pi * Real.exp (403 / 400 : ℝ) ≤ (17208047920375403 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell805_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell805_endpointLower :
    (229983847 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (161 / 320 : ℝ) (403 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (268539778536027 / 31250000000000 : ℝ) (Real.pi * Real.exp (161 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell805_product_lower
  have hD : Real.exp (Real.pi * Real.exp (403 / 400 : ℝ) - (161 / 640 : ℝ)) ≤
      (2120302995029 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell805_denomUpper
    linarith [hpThetaJensenCell805_product_upper]
  have hi : (1 / (2120302995029 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (403 / 400 : ℝ) - (161 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2120302995029 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2120302995029 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((161 / 640 : ℝ) - Real.pi * Real.exp (403 / 400 : ℝ)) := by
    rw [show (161 / 640 : ℝ) - Real.pi * Real.exp (403 / 400 : ℝ) =
      -(Real.pi * Real.exp (403 / 400 : ℝ) - (161 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (161 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (161 / 160 : ℝ)) := by
    have h := hpThetaJensenCell805_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2120302995029 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell805_endpointUpper :
    hpThetaJensenKernelEndpointUpper (161 / 320 : ℝ) (403 / 800 : ℝ) ≤ (1169001731 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (403 / 400 : ℝ)) (17208047920375403 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (403 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell805_product_upper
  have hD : (41939484211947 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (161 / 160 : ℝ) - (403 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell805_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell805_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (161 / 160 : ℝ) - (403 / 1600 : ℝ)) ≤
      (1 / (41939484211947 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (41939484211947 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((403 / 1600 : ℝ) - Real.pi * Real.exp (161 / 160 : ℝ)) ≤
      (2 / (41939484211947 / 10000000000 : ℝ) : ℝ) := by
    rw [show (403 / 1600 : ℝ) - Real.pi * Real.exp (161 / 160 : ℝ) =
      -(Real.pi * Real.exp (161 / 160 : ℝ) - (403 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (17208047920375403 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (17208047920375403 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell805_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (161 / 320 : ℝ) (403 / 800 : ℝ)) :
    (229983847 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1169001731 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell805_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell805_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell806_leftExp :
    (27387455853 / 10000000000 : ℝ) ≤ Real.exp (403 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (403 / 400 : ℝ) (10319852507 / 10000000000 : ℝ)
    (27387455853 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell806_rightExp :
    Real.exp (807 / 800 : ℝ) ≤ (1371085579 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (807 / 800 : ℝ) (258006390853 / 250000000000 : ℝ)
    (1371085579 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell806_denomUpper :
    Real.exp (4181455357387347 / 500000000000000 : ℝ) ≤ (21425747397273 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4181455357387347 / 500000000000000 : ℝ) (1298670384397 /
    1000000000000 : ℝ) (21425747397273 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell806_denomLower :
    (2118972414969 / 500000000 : ℝ) ≤ Real.exp (10439792151017247 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10439792151017247 / 1250000000000000 : ℝ) (81138807473 /
    62500000000 : ℝ) (2118972414969 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell806_product_lower :
    (10755026526017247 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (403 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell806_leftExp
    (by norm_num : (0 : ℝ) ≤ (27387455853 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell806_product_upper :
    Real.pi * Real.exp (807 / 800 : ℝ) ≤ (4307392857387347 / 500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell806_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell806_endpointLower :
    (1141115839 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (403 / 800 : ℝ) (807 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10755026526017247 / 1250000000000000 : ℝ) (Real.pi * Real.exp (403 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell806_product_lower
  have hD : Real.exp (Real.pi * Real.exp (807 / 800 : ℝ) - (403 / 1600 : ℝ)) ≤
      (21425747397273 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell806_denomUpper
    linarith [hpThetaJensenCell806_product_upper]
  have hi : (1 / (21425747397273 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (807 / 800 : ℝ) - (403 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (21425747397273 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (21425747397273 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((403 / 1600 : ℝ) - Real.pi * Real.exp (807 / 800 : ℝ)) := by
    rw [show (403 / 1600 : ℝ) - Real.pi * Real.exp (807 / 800 : ℝ) =
      -(Real.pi * Real.exp (807 / 800 : ℝ) - (403 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (403 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (403 / 400 : ℝ)) := by
    have h := hpThetaJensenCell806_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (21425747397273 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell806_endpointUpper :
    hpThetaJensenKernelEndpointUpper (403 / 800 : ℝ) (807 / 1600 : ℝ) ≤ (1160067381 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (807 / 800 : ℝ)) (4307392857387347 / 500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (807 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell806_product_upper
  have hD : (2118972414969 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (403 / 400 : ℝ) - (807 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell806_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell806_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (403 / 400 : ℝ) - (807 / 3200 : ℝ)) ≤
      (1 / (2118972414969 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2118972414969 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((807 / 3200 : ℝ) - Real.pi * Real.exp (403 / 400 : ℝ)) ≤
      (2 / (2118972414969 / 500000000 : ℝ) : ℝ) := by
    rw [show (807 / 3200 : ℝ) - Real.pi * Real.exp (403 / 400 : ℝ) =
      -(Real.pi * Real.exp (403 / 400 : ℝ) - (807 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4307392857387347 / 500000000000000 : ℝ) ^ 2 - 6 *
      (4307392857387347 / 500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell806_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (403 / 800 : ℝ) (807 / 1600 : ℝ)) :
    (1141115839 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1160067381 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell806_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell806_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell807_leftExp :
    (13710855789 / 5000000000 : ℝ) ≤ Real.exp (807 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (807 / 800 : ℝ) (1032025563411 / 1000000000000 : ℝ)
    (13710855789 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell807_rightExp :
    Real.exp (101 / 100 : ℝ) ≤ (27456010151 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (101 / 100 : ℝ) (516032938849 / 500000000000 : ℝ)
    (27456010151 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell807_denomUpper :
    Real.exp (83733734298310543 / 10000000000000000 : ℝ) ≤ (43302191418583 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (83733734298310543 / 10000000000000000 : ℝ)
    (1299095066889 / 1000000000000 : ℝ) (43302191418583 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell807_denomLower :
    (42824603517819 / 10000000000 : ℝ) ≤ Real.exp (5226426857484511 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5226426857484511 / 625000000000000 : ℝ) (649322454339 /
    500000000000 : ℝ) (42824603517819 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell807_product_lower :
    (5384239357484511 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (807 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell807_leftExp
    (by norm_num : (0 : ℝ) ≤ (13710855789 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell807_product_upper :
    Real.pi * Real.exp (101 / 100 : ℝ) ≤ (86255609298310543 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell807_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell807_endpointLower :
    (70772759 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (807 / 1600 : ℝ) (101 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5384239357484511 / 625000000000000 : ℝ) (Real.pi * Real.exp (807 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell807_product_lower
  have hD : Real.exp (Real.pi * Real.exp (101 / 100 : ℝ) - (807 / 3200 : ℝ)) ≤
      (43302191418583 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell807_denomUpper
    linarith [hpThetaJensenCell807_product_upper]
  have hi : (1 / (43302191418583 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (101 / 100 : ℝ) - (807 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (43302191418583 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (43302191418583 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((807 / 3200 : ℝ) - Real.pi * Real.exp (101 / 100 : ℝ)) := by
    rw [show (807 / 3200 : ℝ) - Real.pi * Real.exp (101 / 100 : ℝ) =
      -(Real.pi * Real.exp (101 / 100 : ℝ) - (807 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (807 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (807 / 800 : ℝ)) := by
    have h := hpThetaJensenCell807_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (43302191418583 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell807_endpointUpper :
    hpThetaJensenKernelEndpointUpper (807 / 1600 : ℝ) (101 / 200 : ℝ) ≤ (1151185379 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (101 / 100 : ℝ)) (86255609298310543 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (101 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell807_product_upper
  have hD : (42824603517819 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (807 / 800 : ℝ) - (101 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell807_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell807_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (807 / 800 : ℝ) - (101 / 400 : ℝ)) ≤
      (1 / (42824603517819 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (42824603517819 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((101 / 400 : ℝ) - Real.pi * Real.exp (807 / 800 : ℝ)) ≤
      (2 / (42824603517819 / 10000000000 : ℝ) : ℝ) := by
    rw [show (101 / 400 : ℝ) - Real.pi * Real.exp (807 / 800 : ℝ) =
      -(Real.pi * Real.exp (807 / 800 : ℝ) - (101 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (86255609298310543 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (86255609298310543 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell807_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (807 / 1600 : ℝ) (101 / 200 : ℝ)) :
    (70772759 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1151185379 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell807_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell807_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell808_leftExp :
    (27456010149 / 10000000000 : ℝ) ≤ Real.exp (101 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (101 / 100 : ℝ) (1032065877697 / 1000000000000 : ℝ)
    (27456010149 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell808_rightExp :
    Real.exp (809 / 800 : ℝ) ≤ (27490351623 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (809 / 800 : ℝ) (1032106193559 / 1000000000000 : ℝ)
    (27490351623 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell808_denomUpper :
    Real.exp (83838496226355439 / 10000000000000000 : ℝ) ≤ (10939554516441 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (83838496226355439 / 10000000000000000 : ℝ)
    (1299520435589 / 1000000000000 : ℝ) (10939554516441 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell808_denomLower :
    (1731000686389 / 400000000 : ℝ) ≤ Real.exp (10465932104502151 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10465932104502151 / 1250000000000000 : ℝ) (1299069582699
    / 1000000000000 : ℝ) (1731000686389 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell808_product_lower :
    (10781947729502151 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (101 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell808_leftExp
    (by norm_num : (0 : ℝ) ≤ (27456010149 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell808_product_upper :
    Real.pi * Real.exp (809 / 800 : ℝ) ≤ (86363496226355439 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell808_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell808_endpointLower :
    (1123663977 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (101 / 200 : ℝ) (809 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10781947729502151 / 1250000000000000 : ℝ) (Real.pi * Real.exp (101 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell808_product_lower
  have hD : Real.exp (Real.pi * Real.exp (809 / 800 : ℝ) - (101 / 400 : ℝ)) ≤
      (10939554516441 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell808_denomUpper
    linarith [hpThetaJensenCell808_product_upper]
  have hi : (1 / (10939554516441 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (809 / 800 : ℝ) - (101 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (10939554516441 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (10939554516441 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((101 / 400 : ℝ) - Real.pi * Real.exp (809 / 800 : ℝ)) := by
    rw [show (101 / 400 : ℝ) - Real.pi * Real.exp (809 / 800 : ℝ) =
      -(Real.pi * Real.exp (809 / 800 : ℝ) - (101 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (101 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (101 / 100 : ℝ)) := by
    have h := hpThetaJensenCell808_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (10939554516441 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell808_endpointUpper :
    hpThetaJensenKernelEndpointUpper (101 / 200 : ℝ) (809 / 1600 : ℝ) ≤ (22847111 / 200000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (809 / 800 : ℝ)) (86363496226355439 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (809 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell808_product_upper
  have hD : (1731000686389 / 400000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (101 / 100 : ℝ) - (809 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell808_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell808_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (101 / 100 : ℝ) - (809 / 3200 : ℝ)) ≤
      (1 / (1731000686389 / 400000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1731000686389 / 400000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((809 / 3200 : ℝ) - Real.pi * Real.exp (101 / 100 : ℝ)) ≤
      (2 / (1731000686389 / 400000000 : ℝ) : ℝ) := by
    rw [show (809 / 3200 : ℝ) - Real.pi * Real.exp (101 / 100 : ℝ) =
      -(Real.pi * Real.exp (101 / 100 : ℝ) - (809 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (86363496226355439 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (86363496226355439 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell808_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (101 / 200 : ℝ) (809 / 1600 : ℝ)) :
    (1123663977 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (22847111 / 200000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell808_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell808_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell809_leftExp :
    (27490351621 / 10000000000 : ℝ) ≤ Real.exp (809 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (809 / 800 : ℝ) (516053096779 / 500000000000 : ℝ)
    (27490351621 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell809_rightExp :
    Real.exp (81 / 80 : ℝ) ≤ (1720296003 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (81 / 80 : ℝ) (516073255497 / 500000000000 : ℝ)
    (1720296003 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell809_denomUpper :
    Real.exp (5246462068452779 / 625000000000000 : ℝ) ≤ (44219643946807 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (5246462068452779 / 625000000000000 : ℝ) (1299946491743 /
    1000000000000 : ℝ) (44219643946807 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell809_denomLower :
    (43730757477389 / 10000000000 : ℝ) ≤ Real.exp (10479027341215079 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10479027341215079 / 1250000000000000 : ℝ) (259898988583
    / 200000000000 : ℝ) (43730757477389 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell809_product_lower :
    (10795433591215079 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (809 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell809_leftExp
    (by norm_num : (0 : ℝ) ≤ (27490351621 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell809_product_upper :
    Real.pi * Real.exp (81 / 80 : ℝ) ≤ (5404469880952779 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell809_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell809_endpointLower :
    (223003033 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (809 / 1600 : ℝ) (81 / 160 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10795433591215079 / 1250000000000000 : ℝ) (Real.pi * Real.exp (809 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell809_product_lower
  have hD : Real.exp (Real.pi * Real.exp (81 / 80 : ℝ) - (809 / 3200 : ℝ)) ≤
      (44219643946807 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell809_denomUpper
    linarith [hpThetaJensenCell809_product_upper]
  have hi : (1 / (44219643946807 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (81 / 80 : ℝ) - (809 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (44219643946807 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (44219643946807 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((809 / 3200 : ℝ) - Real.pi * Real.exp (81 / 80 : ℝ)) := by
    rw [show (809 / 3200 : ℝ) - Real.pi * Real.exp (81 / 80 : ℝ) =
      -(Real.pi * Real.exp (81 / 80 : ℝ) - (809 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (809 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (809 / 800 : ℝ)) := by
    have h := hpThetaJensenCell809_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (44219643946807 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell809_endpointUpper :
    hpThetaJensenKernelEndpointUpper (809 / 1600 : ℝ) (81 / 160 : ℝ) ≤ (1133577719 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (81 / 80 : ℝ)) (5404469880952779 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (81 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell809_product_upper
  have hD : (43730757477389 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (809 / 800 : ℝ) - (81 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell809_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell809_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (809 / 800 : ℝ) - (81 / 320 : ℝ)) ≤
      (1 / (43730757477389 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (43730757477389 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((81 / 320 : ℝ) - Real.pi * Real.exp (809 / 800 : ℝ)) ≤
      (2 / (43730757477389 / 10000000000 : ℝ) : ℝ) := by
    rw [show (81 / 320 : ℝ) - Real.pi * Real.exp (809 / 800 : ℝ) =
      -(Real.pi * Real.exp (809 / 800 : ℝ) - (81 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (5404469880952779 / 625000000000000 : ℝ) ^ 2 - 6 *
      (5404469880952779 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell809_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (809 / 1600 : ℝ) (81 / 160 : ℝ)) :
    (223003033 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1133577719 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell809_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell809_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell810_leftExp :
    (13762368023 / 5000000000 : ℝ) ≤ Real.exp (81 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (81 / 80 : ℝ) (1032146510993 / 1000000000000 : ℝ)
    (13762368023 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell810_rightExp :
    Real.exp (811 / 800 : ℝ) ≤ (27559163481 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (811 / 800 : ℝ) (206437366001 / 200000000000 : ℝ)
    (27559163481 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell810_denomUpper :
    Real.exp (84048425077765233 / 10000000000000000 : ℝ) ≤ (44686539289247 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (84048425077765233 / 10000000000000000 : ℝ) (8127332729 /
    6250000000 : ℝ) (44686539289247 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell810_denomLower :
    (5523986704761 / 1250000000 : ℝ) ≤ Real.exp (5246069722764077 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5246069722764077 / 625000000000000 : ℝ) (324980247643 /
    250000000000 : ℝ) (5523986704761 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell810_product_lower :
    (5404468160264077 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (81 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell810_leftExp
    (by norm_num : (0 : ℝ) ≤ (13762368023 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell810_product_upper :
    Real.pi * Real.exp (811 / 800 : ℝ) ≤ (86579675077765233 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell810_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell810_endpointLower :
    (1106417533 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (81 / 160 : ℝ) (811 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5404468160264077 / 625000000000000 : ℝ) (Real.pi * Real.exp (81 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell810_product_lower
  have hD : Real.exp (Real.pi * Real.exp (811 / 800 : ℝ) - (81 / 320 : ℝ)) ≤
      (44686539289247 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell810_denomUpper
    linarith [hpThetaJensenCell810_product_upper]
  have hi : (1 / (44686539289247 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (811 / 800 : ℝ) - (81 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (44686539289247 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (44686539289247 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((81 / 320 : ℝ) - Real.pi * Real.exp (811 / 800 : ℝ)) := by
    rw [show (81 / 320 : ℝ) - Real.pi * Real.exp (811 / 800 : ℝ) =
      -(Real.pi * Real.exp (811 / 800 : ℝ) - (81 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (81 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (81 / 80 : ℝ)) := by
    have h := hpThetaJensenCell810_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (44686539289247 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell810_endpointUpper :
    hpThetaJensenKernelEndpointUpper (81 / 160 : ℝ) (811 / 1600 : ℝ) ≤ (1124851711 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (811 / 800 : ℝ)) (86579675077765233 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (811 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell810_product_upper
  have hD : (5523986704761 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (81 / 80 : ℝ) - (811 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell810_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell810_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (81 / 80 : ℝ) - (811 / 3200 : ℝ)) ≤
      (1 / (5523986704761 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5523986704761 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((811 / 3200 : ℝ) - Real.pi * Real.exp (81 / 80 : ℝ)) ≤
      (2 / (5523986704761 / 1250000000 : ℝ) : ℝ) := by
    rw [show (811 / 3200 : ℝ) - Real.pi * Real.exp (81 / 80 : ℝ) =
      -(Real.pi * Real.exp (81 / 80 : ℝ) - (811 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (86579675077765233 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (86579675077765233 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell810_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (81 / 160 : ℝ) (811 / 1600 : ℝ)) :
    (1106417533 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1124851711 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell810_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell810_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell811_leftExp :
    (27559163479 / 10000000000 : ℝ) ≤ Real.exp (811 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (811 / 800 : ℝ) (258046707501 / 250000000000 : ℝ)
    (27559163479 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell811_rightExp :
    Real.exp (203 / 200 : ℝ) ≤ (13796816987 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (203 / 200 : ℝ) (103222715059 / 100000000000 : ℝ)
    (13796816987 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell811_denomUpper :
    Real.exp (42076796168640291 / 5000000000000000 : ℝ) ≤ (22579487631063 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (42076796168640291 / 5000000000000000 : ℝ) (1300800671529
    / 1000000000000 : ℝ) (22579487631063 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell811_denomLower :
    (44658495824177 / 10000000000 : ℝ) ≤ Real.exp (10505268439039821 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10505268439039821 / 1250000000000000 : ℝ) (650173863479
    / 500000000000 : ℝ) (44658495824177 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell811_product_lower :
    (10822455939039821 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (811 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell811_leftExp
    (by norm_num : (0 : ℝ) ≤ (27559163479 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell811_product_upper :
    Real.pi * Real.exp (203 / 200 : ℝ) ≤ (43343983668640291 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell811_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell811_endpointLower :
    (274467727 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (811 / 1600 : ℝ) (203 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10822455939039821 / 1250000000000000 : ℝ) (Real.pi * Real.exp (811 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell811_product_lower
  have hD : Real.exp (Real.pi * Real.exp (203 / 200 : ℝ) - (811 / 3200 : ℝ)) ≤
      (22579487631063 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell811_denomUpper
    linarith [hpThetaJensenCell811_product_upper]
  have hi : (1 / (22579487631063 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (203 / 200 : ℝ) - (811 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (22579487631063 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (22579487631063 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((811 / 3200 : ℝ) - Real.pi * Real.exp (203 / 200 : ℝ)) := by
    rw [show (811 / 3200 : ℝ) - Real.pi * Real.exp (203 / 200 : ℝ) =
      -(Real.pi * Real.exp (203 / 200 : ℝ) - (811 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (811 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (811 / 800 : ℝ)) := by
    have h := hpThetaJensenCell811_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (22579487631063 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell811_endpointUpper :
    hpThetaJensenKernelEndpointUpper (811 / 1600 : ℝ) (203 / 400 : ℝ) ≤ (22323547 / 200000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (203 / 200 : ℝ)) (43343983668640291 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (203 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell811_product_upper
  have hD : (44658495824177 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (811 / 800 : ℝ) - (203 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell811_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell811_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (811 / 800 : ℝ) - (203 / 800 : ℝ)) ≤
      (1 / (44658495824177 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (44658495824177 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((203 / 800 : ℝ) - Real.pi * Real.exp (811 / 800 : ℝ)) ≤
      (2 / (44658495824177 / 10000000000 : ℝ) : ℝ) := by
    rw [show (203 / 800 : ℝ) - Real.pi * Real.exp (811 / 800 : ℝ) =
      -(Real.pi * Real.exp (811 / 800 : ℝ) - (203 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (43343983668640291 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (43343983668640291 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell811_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (811 / 1600 : ℝ) (203 / 400 : ℝ)) :
    (274467727 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (22323547 / 200000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell811_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell811_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell812_leftExp :
    (27593633973 / 10000000000 : ℝ) ≤ Real.exp (203 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (203 / 200 : ℝ) (1032227150589 / 1000000000000 : ℝ)
    (27593633973 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell812_rightExp :
    Real.exp (813 / 800 : ℝ) ≤ (215844903 / 78125000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (813 / 800 : ℝ) (1032267472751 / 1000000000000 : ℝ)
    (215844903 / 78125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell812_denomUpper :
    Real.exp (658272617600479 / 78125000000000 : ℝ) ≤ (5704628013711 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (658272617600479 / 78125000000000 : ℝ) (1301228797727 /
    1000000000000 : ℝ) (5704628013711 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell812_denomLower :
    (45130635173317 / 10000000000 : ℝ) ≤ Real.exp (10518414342563127 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10518414342563127 / 1250000000000000 : ℝ) (650387576667
    / 500000000000 : ℝ) (45130635173317 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell812_product_lower :
    (10835992467563127 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (203 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell812_leftExp
    (by norm_num : (0 : ℝ) ≤ (27593633973 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell812_product_upper :
    Real.pi * Real.exp (813 / 800 : ℝ) ≤ (678096836350479 / 78125000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell812_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell812_endpointLower :
    (217875023 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (203 / 400 : ℝ) (813 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10835992467563127 / 1250000000000000 : ℝ) (Real.pi * Real.exp (203 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell812_product_lower
  have hD : Real.exp (Real.pi * Real.exp (813 / 800 : ℝ) - (203 / 800 : ℝ)) ≤
      (5704628013711 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell812_denomUpper
    linarith [hpThetaJensenCell812_product_upper]
  have hi : (1 / (5704628013711 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (813 / 800 : ℝ) - (203 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5704628013711 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5704628013711 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((203 / 800 : ℝ) - Real.pi * Real.exp (813 / 800 : ℝ)) := by
    rw [show (203 / 800 : ℝ) - Real.pi * Real.exp (813 / 800 : ℝ) =
      -(Real.pi * Real.exp (813 / 800 : ℝ) - (203 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (203 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (203 / 200 : ℝ)) := by
    have h := hpThetaJensenCell812_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5704628013711 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell812_endpointUpper :
    hpThetaJensenKernelEndpointUpper (203 / 400 : ℝ) (813 / 1600 : ℝ) ≤ (553777231 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (813 / 800 : ℝ)) (678096836350479 / 78125000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (813 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell812_product_upper
  have hD : (45130635173317 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (203 / 200 : ℝ) - (813 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell812_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell812_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (203 / 200 : ℝ) - (813 / 3200 : ℝ)) ≤
      (1 / (45130635173317 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (45130635173317 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((813 / 3200 : ℝ) - Real.pi * Real.exp (203 / 200 : ℝ)) ≤
      (2 / (45130635173317 / 10000000000 : ℝ) : ℝ) := by
    rw [show (813 / 3200 : ℝ) - Real.pi * Real.exp (203 / 200 : ℝ) =
      -(Real.pi * Real.exp (203 / 200 : ℝ) - (813 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (678096836350479 / 78125000000000 : ℝ) ^ 2 - 6 *
      (678096836350479 / 78125000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell812_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (203 / 400 : ℝ) (813 / 1600 : ℝ)) :
    (217875023 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (553777231 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell812_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell812_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell813_leftExp :
    (13814073791 / 5000000000 : ℝ) ≤ Real.exp (813 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (813 / 800 : ℝ) (4129069891 / 4000000000 : ℝ)
    (13814073791 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell813_rightExp :
    Real.exp (407 / 400 : ℝ) ≤ (13831352181 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (407 / 400 : ℝ) (1032307796487 / 1000000000000 : ℝ)
    (13831352181 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell813_denomUpper :
    Real.exp (42182166692364333 / 5000000000000000 : ℝ) ≤ (46120759006963 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (42182166692364333 / 5000000000000000 : ℝ) (52066304659 /
    40000000000 : ℝ) (46120759006963 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell813_denomLower :
    (570104798041 / 125000000 : ℝ) ≤ Real.exp (5265788588651909 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5265788588651909 / 625000000000000 : ℝ) (65060163549 /
    50000000000 : ℝ) (570104798041 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell813_product_lower :
    (5424772963651909 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (813 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell813_leftExp
    (by norm_num : (0 : ℝ) ≤ (13814073791 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell813_product_upper :
    Real.pi * Real.exp (407 / 400 : ℝ) ≤ (43452479192364333 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell813_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell813_endpointLower :
    (1080929979 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (813 / 1600 : ℝ) (407 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5424772963651909 / 625000000000000 : ℝ) (Real.pi * Real.exp (813 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell813_product_lower
  have hD : Real.exp (Real.pi * Real.exp (407 / 400 : ℝ) - (813 / 3200 : ℝ)) ≤
      (46120759006963 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell813_denomUpper
    linarith [hpThetaJensenCell813_product_upper]
  have hi : (1 / (46120759006963 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (407 / 400 : ℝ) - (813 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (46120759006963 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (46120759006963 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((813 / 3200 : ℝ) - Real.pi * Real.exp (407 / 400 : ℝ)) := by
    rw [show (813 / 3200 : ℝ) - Real.pi * Real.exp (407 / 400 : ℝ) =
      -(Real.pi * Real.exp (407 / 400 : ℝ) - (813 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (813 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (813 / 800 : ℝ)) := by
    have h := hpThetaJensenCell813_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (46120759006963 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell813_endpointUpper :
    hpThetaJensenKernelEndpointUpper (813 / 1600 : ℝ) (407 / 800 : ℝ) ≤ (1098982869 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (407 / 400 : ℝ)) (43452479192364333 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (407 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell813_product_upper
  have hD : (570104798041 / 125000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (813 / 800 : ℝ) - (407 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell813_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell813_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (813 / 800 : ℝ) - (407 / 1600 : ℝ)) ≤
      (1 / (570104798041 / 125000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (570104798041 / 125000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((407 / 1600 : ℝ) - Real.pi * Real.exp (813 / 800 : ℝ)) ≤
      (2 / (570104798041 / 125000000 : ℝ) : ℝ) := by
    rw [show (407 / 1600 : ℝ) - Real.pi * Real.exp (813 / 800 : ℝ) =
      -(Real.pi * Real.exp (813 / 800 : ℝ) - (407 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (43452479192364333 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (43452479192364333 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell813_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (813 / 1600 : ℝ) (407 / 800 : ℝ)) :
    (1080929979 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1098982869 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell813_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell813_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell814_leftExp :
    (691567609 / 250000000 : ℝ) ≤ Real.exp (407 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (407 / 400 : ℝ) (516153898243 / 500000000000 : ℝ)
    (691567609 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell814_rightExp :
    Real.exp (163 / 160 : ℝ) ≤ (27697304363 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (163 / 160 : ℝ) (516174060899 / 500000000000 : ℝ)
    (27697304363 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell814_denomUpper :
    Real.exp (84469907505670259 / 10000000000000000 : ℝ) ≤ (23305127110909 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (84469907505670259 / 10000000000000000 : ℝ) (130208712907
    / 100000000000 : ℝ) (23305127110909 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell814_denomLower :
    (11522953751617 / 2500000000 : ℝ) ≤ Real.exp (263618924111691 / 31250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (263618924111691 / 31250000000000 : ℝ) (162704010147 /
    125000000000 : ℝ) (11522953751617 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell814_product_lower :
    (271577908486691 / 31250000000000 : ℝ) ≤ Real.pi * Real.exp (407 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell814_leftExp
    (by norm_num : (0 : ℝ) ≤ (691567609 / 250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell814_product_upper :
    Real.pi * Real.exp (163 / 160 : ℝ) ≤ (87013657505670259 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell814_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell814_endpointLower :
    (42901413 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (407 / 800 : ℝ) (163 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (271577908486691 / 31250000000000 : ℝ) (Real.pi * Real.exp (407 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell814_product_lower
  have hD : Real.exp (Real.pi * Real.exp (163 / 160 : ℝ) - (407 / 1600 : ℝ)) ≤
      (23305127110909 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell814_denomUpper
    linarith [hpThetaJensenCell814_product_upper]
  have hi : (1 / (23305127110909 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (163 / 160 : ℝ) - (407 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (23305127110909 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (23305127110909 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((407 / 1600 : ℝ) - Real.pi * Real.exp (163 / 160 : ℝ)) := by
    rw [show (407 / 1600 : ℝ) - Real.pi * Real.exp (163 / 160 : ℝ) =
      -(Real.pi * Real.exp (163 / 160 : ℝ) - (407 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (407 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (407 / 400 : ℝ)) := by
    have h := hpThetaJensenCell814_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (23305127110909 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell814_endpointUpper :
    hpThetaJensenKernelEndpointUpper (407 / 800 : ℝ) (163 / 320 : ℝ) ≤ (218092479 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (163 / 160 : ℝ)) (87013657505670259 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (163 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell814_product_upper
  have hD : (11522953751617 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (407 / 400 : ℝ) - (163 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell814_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell814_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (407 / 400 : ℝ) - (163 / 640 : ℝ)) ≤
      (1 / (11522953751617 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (11522953751617 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((163 / 640 : ℝ) - Real.pi * Real.exp (407 / 400 : ℝ)) ≤
      (2 / (11522953751617 / 2500000000 : ℝ) : ℝ) := by
    rw [show (163 / 640 : ℝ) - Real.pi * Real.exp (407 / 400 : ℝ) =
      -(Real.pi * Real.exp (407 / 400 : ℝ) - (163 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (87013657505670259 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (87013657505670259 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell814_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (407 / 800 : ℝ) (163 / 320 : ℝ)) :
    (42901413 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (218092479 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell814_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell814_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell815_leftExp :
    (27697304361 / 10000000000 : ℝ) ≤ Real.exp (163 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (163 / 160 : ℝ) (1032348121797 / 1000000000000 : ℝ)
    (27697304361 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell815_rightExp :
    Real.exp (51 / 50 : ℝ) ≤ (27731947641 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (51 / 50 : ℝ) (258097112171 / 250000000000 : ℝ)
    (27731947641 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell815_denomUpper :
    Real.exp (84575617585332113 / 10000000000000000 : ℝ) ≤ (1472049532823 / 312500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (84575617585332113 / 10000000000000000 : ℝ)
    (1302517336793 / 1000000000000 : ℝ) (1472049532823 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell815_denomLower :
    (5822625358283 / 1250000000 : ℝ) ≤ Real.exp (10557953725260339 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10557953725260339 / 1250000000000000 : ℝ) (1302061585203
    / 1000000000000 : ℝ) (5822625358283 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell815_product_lower :
    (10876703725260339 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (163 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell815_leftExp
    (by norm_num : (0 : ℝ) ≤ (27697304361 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell815_product_upper :
    Real.pi * Real.exp (51 / 50 : ℝ) ≤ (87122492585332113 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell815_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell815_endpointLower :
    (1064190977 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (163 / 320 : ℝ) (51 / 100 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10876703725260339 / 1250000000000000 : ℝ) (Real.pi * Real.exp (163 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell815_product_lower
  have hD : Real.exp (Real.pi * Real.exp (51 / 50 : ℝ) - (163 / 640 : ℝ)) ≤
      (1472049532823 / 312500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell815_denomUpper
    linarith [hpThetaJensenCell815_product_upper]
  have hi : (1 / (1472049532823 / 312500000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (51 / 50 : ℝ) - (163 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1472049532823 / 312500000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1472049532823 / 312500000 : ℝ) : ℝ) ≤
      2 * Real.exp ((163 / 640 : ℝ) - Real.pi * Real.exp (51 / 50 : ℝ)) := by
    rw [show (163 / 640 : ℝ) - Real.pi * Real.exp (51 / 50 : ℝ) =
      -(Real.pi * Real.exp (51 / 50 : ℝ) - (163 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (163 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (163 / 160 : ℝ)) := by
    have h := hpThetaJensenCell815_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1472049532823 / 312500000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell815_endpointUpper :
    hpThetaJensenKernelEndpointUpper (163 / 320 : ℝ) (51 / 100 : ℝ) ≤ (1081992863 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (51 / 50 : ℝ)) (87122492585332113 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (51 / 100 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell815_product_upper
  have hD : (5822625358283 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (163 / 160 : ℝ) - (51 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell815_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell815_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (163 / 160 : ℝ) - (51 / 200 : ℝ)) ≤
      (1 / (5822625358283 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5822625358283 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((51 / 200 : ℝ) - Real.pi * Real.exp (163 / 160 : ℝ)) ≤
      (2 / (5822625358283 / 1250000000 : ℝ) : ℝ) := by
    rw [show (51 / 200 : ℝ) - Real.pi * Real.exp (163 / 160 : ℝ) =
      -(Real.pi * Real.exp (163 / 160 : ℝ) - (51 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (87122492585332113 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (87122492585332113 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell815_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (163 / 320 : ℝ) (51 / 100 : ℝ)) :
    (1064190977 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1081992863 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell815_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell815_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell816_leftExp :
    (27731947639 / 10000000000 : ℝ) ≤ Real.exp (51 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (51 / 50 : ℝ) (1032388448683 / 1000000000000 : ℝ)
    (27731947639 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell816_rightExp :
    Real.exp (817 / 800 : ℝ) ≤ (111066537 / 40000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (817 / 800 : ℝ) (206485755429 / 200000000000 : ℝ)
    (111066537 / 40000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell816_denomUpper :
    Real.exp (338725855173441 / 40000000000000 : ℝ) ≤ (11901706964623 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (338725855173441 / 40000000000000 : ℝ) (325737060233 /
    250000000000 : ℝ) (11901706964623 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell816_denomLower :
    (9415204535203 / 2000000000 : ℝ) ≤ Real.exp (10571167480887661 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10571167480887661 / 1250000000000000 : ℝ) (651245892173
    / 500000000000 : ℝ) (9415204535203 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell816_product_lower :
    (10890308105887661 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (51 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell816_leftExp
    (by norm_num : (0 : ℝ) ≤ (27731947639 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell816_product_upper :
    Real.pi * Real.exp (817 / 800 : ℝ) ≤ (348925855173441 / 40000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell816_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell816_endpointLower :
    (1055896759 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (51 / 100 : ℝ) (817 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10890308105887661 / 1250000000000000 : ℝ) (Real.pi * Real.exp (51 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell816_product_lower
  have hD : Real.exp (Real.pi * Real.exp (817 / 800 : ℝ) - (51 / 200 : ℝ)) ≤
      (11901706964623 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell816_denomUpper
    linarith [hpThetaJensenCell816_product_upper]
  have hi : (1 / (11901706964623 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (817 / 800 : ℝ) - (51 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (11901706964623 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (11901706964623 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((51 / 200 : ℝ) - Real.pi * Real.exp (817 / 800 : ℝ)) := by
    rw [show (51 / 200 : ℝ) - Real.pi * Real.exp (817 / 800 : ℝ) =
      -(Real.pi * Real.exp (817 / 800 : ℝ) - (51 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (51 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (51 / 50 : ℝ)) := by
    have h := hpThetaJensenCell816_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (11901706964623 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell816_endpointUpper :
    hpThetaJensenKernelEndpointUpper (51 / 100 : ℝ) (817 / 1600 : ℝ) ≤ (214714819 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (817 / 800 : ℝ)) (348925855173441 / 40000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (817 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell816_product_upper
  have hD : (9415204535203 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (51 / 50 : ℝ) - (817 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell816_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell816_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (51 / 50 : ℝ) - (817 / 3200 : ℝ)) ≤
      (1 / (9415204535203 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (9415204535203 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((817 / 3200 : ℝ) - Real.pi * Real.exp (51 / 50 : ℝ)) ≤
      (2 / (9415204535203 / 2000000000 : ℝ) : ℝ) := by
    rw [show (817 / 3200 : ℝ) - Real.pi * Real.exp (51 / 50 : ℝ) =
      -(Real.pi * Real.exp (51 / 50 : ℝ) - (817 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (348925855173441 / 40000000000000 : ℝ) ^ 2 - 6 *
      (348925855173441 / 40000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell816_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (51 / 100 : ℝ) (817 / 1600 : ℝ)) :
    (1055896759 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (214714819 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell816_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell816_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell817_leftExp :
    (3470829281 / 1250000000 : ℝ) ≤ Real.exp (817 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (817 / 800 : ℝ) (129053597143 / 125000000000 : ℝ)
    (3470829281 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell817_rightExp :
    Real.exp (409 / 400 : ℝ) ≤ (6950341061 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (409 / 400 : ℝ) (516234553591 / 500000000000 : ℝ)
    (6950341061 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell817_denomUpper :
    Real.exp (21196861574850173 / 2500000000000000 : ℝ) ≤ (24057030045129 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21196861574850173 / 2500000000000000 : ℝ) (52135193711 /
    40000000000 : ℝ) (24057030045129 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell817_denomLower :
    (47576950751461 / 10000000000 : ℝ) ≤ Real.exp (1323049781569419 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1323049781569419 / 156250000000000 : ℝ) (1302922679891 /
    1000000000000 : ℝ) (47576950751461 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell817_product_lower :
    (1362991187819419 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (817 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell817_leftExp
    (by norm_num : (0 : ℝ) ≤ (3470829281 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell817_product_upper :
    Real.pi * Real.exp (409 / 400 : ℝ) ≤ (21835142824850173 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell817_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell817_endpointLower :
    (209530499 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (817 / 1600 : ℝ) (409 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1362991187819419 / 156250000000000 : ℝ) (Real.pi * Real.exp (817 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell817_product_lower
  have hD : Real.exp (Real.pi * Real.exp (409 / 400 : ℝ) - (817 / 3200 : ℝ)) ≤
      (24057030045129 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell817_denomUpper
    linarith [hpThetaJensenCell817_product_upper]
  have hi : (1 / (24057030045129 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (409 / 400 : ℝ) - (817 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (24057030045129 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (24057030045129 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((817 / 3200 : ℝ) - Real.pi * Real.exp (409 / 400 : ℝ)) := by
    rw [show (817 / 3200 : ℝ) - Real.pi * Real.exp (409 / 400 : ℝ) =
      -(Real.pi * Real.exp (409 / 400 : ℝ) - (817 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (817 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (817 / 800 : ℝ)) := by
    have h := hpThetaJensenCell817_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (24057030045129 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell817_endpointUpper :
    hpThetaJensenKernelEndpointUpper (817 / 1600 : ℝ) (409 / 800 : ℝ) ≤ (532602957 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (409 / 400 : ℝ)) (21835142824850173 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (409 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell817_product_upper
  have hD : (47576950751461 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (817 / 800 : ℝ) - (409 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell817_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell817_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (817 / 800 : ℝ) - (409 / 1600 : ℝ)) ≤
      (1 / (47576950751461 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (47576950751461 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((409 / 1600 : ℝ) - Real.pi * Real.exp (817 / 800 : ℝ)) ≤
      (2 / (47576950751461 / 10000000000 : ℝ) : ℝ) := by
    rw [show (409 / 1600 : ℝ) - Real.pi * Real.exp (817 / 800 : ℝ) =
      -(Real.pi * Real.exp (817 / 800 : ℝ) - (409 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (21835142824850173 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (21835142824850173 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell817_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (817 / 1600 : ℝ) (409 / 800 : ℝ)) :
    (209530499 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (532602957 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell817_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell817_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell818_leftExp :
    (27801364243 / 10000000000 : ℝ) ≤ Real.exp (409 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (409 / 400 : ℝ) (1032469107181 / 1000000000000 : ℝ)
    (27801364243 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell818_rightExp :
    Real.exp (819 / 800 : ℝ) ≤ (13918068839 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (819 / 800 : ℝ) (516254719397 / 500000000000 : ℝ)
    (13918068839 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell818_denomUpper :
    Real.exp (42446782638120527 / 5000000000000000 : ℝ) ≤ (12156840075133 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (42446782638120527 / 5000000000000000 : ℝ) (162976517953
    / 125000000000 : ℝ) (12156840075133 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell818_denomLower :
    (48083864502099 / 10000000000 : ℝ) ≤ Real.exp (10597646061861857 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10597646061861857 / 1250000000000000 : ℝ) (651677136569
    / 500000000000 : ℝ) (48083864502099 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell818_product_lower :
    (10917567936861857 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (409 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell818_leftExp
    (by norm_num : (0 : ℝ) ≤ (27801364243 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell818_product_upper :
    Real.pi * Real.exp (819 / 800 : ℝ) ≤ (43724907638120527 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell818_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell818_endpointLower :
    (129932251 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (409 / 800 : ℝ) (819 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10917567936861857 / 1250000000000000 : ℝ) (Real.pi * Real.exp (409 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell818_product_lower
  have hD : Real.exp (Real.pi * Real.exp (819 / 800 : ℝ) - (409 / 1600 : ℝ)) ≤
      (12156840075133 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell818_denomUpper
    linarith [hpThetaJensenCell818_product_upper]
  have hi : (1 / (12156840075133 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (819 / 800 : ℝ) - (409 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (12156840075133 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (12156840075133 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((409 / 1600 : ℝ) - Real.pi * Real.exp (819 / 800 : ℝ)) := by
    rw [show (409 / 1600 : ℝ) - Real.pi * Real.exp (819 / 800 : ℝ) =
      -(Real.pi * Real.exp (819 / 800 : ℝ) - (409 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (409 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (409 / 400 : ℝ)) := by
    have h := hpThetaJensenCell818_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (12156840075133 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell818_endpointUpper :
    hpThetaJensenKernelEndpointUpper (409 / 800 : ℝ) (819 / 1600 : ℝ) ≤ (1056888141 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (819 / 800 : ℝ)) (43724907638120527 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (819 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell818_product_upper
  have hD : (48083864502099 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (409 / 400 : ℝ) - (819 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell818_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell818_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (409 / 400 : ℝ) - (819 / 3200 : ℝ)) ≤
      (1 / (48083864502099 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (48083864502099 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((819 / 3200 : ℝ) - Real.pi * Real.exp (409 / 400 : ℝ)) ≤
      (2 / (48083864502099 / 10000000000 : ℝ) : ℝ) := by
    rw [show (819 / 3200 : ℝ) - Real.pi * Real.exp (409 / 400 : ℝ) =
      -(Real.pi * Real.exp (409 / 400 : ℝ) - (819 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (43724907638120527 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (43724907638120527 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell818_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (409 / 800 : ℝ) (819 / 1600 : ℝ)) :
    (129932251 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1056888141 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell818_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell818_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell819_leftExp :
    (6959034419 / 2500000000 : ℝ) ≤ Real.exp (819 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (819 / 800 : ℝ) (1032509438793 / 1000000000000 : ℝ)
    (6959034419 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell819_rightExp :
    Real.exp (41 / 40 : ℝ) ≤ (27870954607 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (41 / 40 : ℝ) (516274885991 / 500000000000 : ℝ)
    (27870954607 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell819_denomUpper :
    Real.exp (84999820896668951 / 10000000000000000 : ℝ) ≤ (24573404080213 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (84999820896668951 / 10000000000000000 : ℝ) (260849028957
    / 200000000000 : ℝ) (24573404080213 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell819_denomLower :
    (12149210597449 / 2500000000 : ℝ) ≤ Real.exp (2652727732306881 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2652727732306881 / 312500000000000 : ℝ) (162973320669 /
    125000000000 : ℝ) (12149210597449 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell819_product_lower :
    (2732805857306881 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (819 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell819_leftExp
    (by norm_num : (0 : ℝ) ≤ (6959034419 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell819_product_upper :
    Real.pi * Real.exp (41 / 40 : ℝ) ≤ (87559195896668951 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell819_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell819_endpointLower :
    (6445707 / 62500000 : ℝ) ≤ hpThetaTraceEndpointLower (819 / 1600 : ℝ) (41 / 80 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2732805857306881 / 312500000000000 : ℝ) (Real.pi * Real.exp (819 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell819_product_lower
  have hD : Real.exp (Real.pi * Real.exp (41 / 40 : ℝ) - (819 / 3200 : ℝ)) ≤
      (24573404080213 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell819_denomUpper
    linarith [hpThetaJensenCell819_product_upper]
  have hi : (1 / (24573404080213 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (41 / 40 : ℝ) - (819 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (24573404080213 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (24573404080213 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((819 / 3200 : ℝ) - Real.pi * Real.exp (41 / 40 : ℝ)) := by
    rw [show (819 / 3200 : ℝ) - Real.pi * Real.exp (41 / 40 : ℝ) =
      -(Real.pi * Real.exp (41 / 40 : ℝ) - (819 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (819 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (819 / 800 : ℝ)) := by
    have h := hpThetaJensenCell819_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (24573404080213 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell819_endpointUpper :
    hpThetaJensenKernelEndpointUpper (819 / 1600 : ℝ) (41 / 80 : ℝ) ≤ (1048620599 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (41 / 40 : ℝ)) (87559195896668951 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (41 / 80 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell819_product_upper
  have hD : (12149210597449 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (819 / 800 : ℝ) - (41 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell819_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell819_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (819 / 800 : ℝ) - (41 / 160 : ℝ)) ≤
      (1 / (12149210597449 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (12149210597449 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((41 / 160 : ℝ) - Real.pi * Real.exp (819 / 800 : ℝ)) ≤
      (2 / (12149210597449 / 2500000000 : ℝ) : ℝ) := by
    rw [show (41 / 160 : ℝ) - Real.pi * Real.exp (819 / 800 : ℝ) =
      -(Real.pi * Real.exp (819 / 800 : ℝ) - (41 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (87559195896668951 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (87559195896668951 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell819_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (819 / 1600 : ℝ) (41 / 80 : ℝ)) :
    (6445707 / 62500000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1048620599 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell819_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell819_endpointUpper

def hpThetaJensenCellsBatch040Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (597358877 / 5000000000 : ℝ)
  | 1 => (592826637 / 5000000000 : ℝ)
  | 2 => (1176641353 / 10000000000 : ℝ)
  | 3 => (58384091 / 500000000 : ℝ)
  | 4 => (231754901 / 2000000000 : ℝ)
  | 5 => (229983847 / 2000000000 : ℝ)
  | 6 => (1141115839 / 10000000000 : ℝ)
  | 7 => (70772759 / 625000000 : ℝ)
  | 8 => (1123663977 / 10000000000 : ℝ)
  | 9 => (223003033 / 2000000000 : ℝ)
  | 10 => (1106417533 / 10000000000 : ℝ)
  | 11 => (274467727 / 2500000000 : ℝ)
  | 12 => (217875023 / 2000000000 : ℝ)
  | 13 => (1080929979 / 10000000000 : ℝ)
  | 14 => (42901413 / 400000000 : ℝ)
  | 15 => (1064190977 / 10000000000 : ℝ)
  | 16 => (1055896759 / 10000000000 : ℝ)
  | 17 => (209530499 / 2000000000 : ℝ)
  | 18 => (129932251 / 1250000000 : ℝ)
  | 19 => (6445707 / 62500000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch040Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (75904047 / 625000000 : ℝ)
  | 1 => (1205266069 / 10000000000 : ℝ)
  | 2 => (598060299 / 5000000000 : ℝ)
  | 3 => (237405633 / 2000000000 : ℝ)
  | 4 => (1177988601 / 10000000000 : ℝ)
  | 5 => (1169001731 / 10000000000 : ℝ)
  | 6 => (1160067381 / 10000000000 : ℝ)
  | 7 => (1151185379 / 10000000000 : ℝ)
  | 8 => (22847111 / 200000000 : ℝ)
  | 9 => (1133577719 / 10000000000 : ℝ)
  | 10 => (1124851711 / 10000000000 : ℝ)
  | 11 => (22323547 / 200000000 : ℝ)
  | 12 => (553777231 / 5000000000 : ℝ)
  | 13 => (1098982869 / 10000000000 : ℝ)
  | 14 => (218092479 / 2000000000 : ℝ)
  | 15 => (1081992863 / 10000000000 : ℝ)
  | 16 => (214714819 / 2000000000 : ℝ)
  | 17 => (532602957 / 5000000000 : ℝ)
  | 18 => (1056888141 / 10000000000 : ℝ)
  | 19 => (1048620599 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch040_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((800 : ℝ) + (j.val : ℝ)) / 1600)
      (((800 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch040Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch040Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell800_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell801_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell802_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell803_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell804_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell805_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell806_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell807_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell808_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell809_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell810_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell811_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell812_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell813_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell814_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell815_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell816_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell817_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell818_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell819_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper] at h ⊢
    exact h

end HodgeProofHP
