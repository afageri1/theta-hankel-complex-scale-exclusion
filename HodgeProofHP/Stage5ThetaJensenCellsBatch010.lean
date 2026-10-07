import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell200_leftExp :
    (6420127083 / 5000000000 : ℝ) ≤ Real.exp (1 / 4 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1 / 4 : ℝ) (503921548603 / 500000000000 : ℝ) (6420127083
    / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell200_rightExp :
    Real.exp (201 / 800 : ℝ) ≤ (12856314521 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (201 / 800 : ℝ) (1007882466847 / 1000000000000 : ℝ)
    (12856314521 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell200_denomUpper :
    Real.exp (39764307704971953 / 10000000000000000 : ℝ) ≤ (66657950167 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (39764307704971953 / 10000000000000000 : ℝ)
    (1132314152979 / 1000000000000 : ℝ) (66657950167 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell200_denomLower :
    (33150833093 / 625000000 : ℝ) ≤ Real.exp (2481919672867017 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2481919672867017 / 625000000000000 : ℝ) (1132124531221 /
    1000000000000 : ℝ) (33150833093 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell200_product_lower :
    (2521177485367017 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1 / 4 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell200_leftExp
    (by norm_num : (0 : ℝ) ≤ (6420127083 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell200_product_upper :
    Real.pi * Real.exp (201 / 800 : ℝ) ≤ (40389307704971953 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell200_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell200_endpointLower :
    (3833523963 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 8 : ℝ) (201 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2521177485367017 / 625000000000000 : ℝ) (Real.pi * Real.exp (1 / 4 : ℝ))
    (by norm_num) hpThetaJensenCell200_product_lower
  have hD : Real.exp (Real.pi * Real.exp (201 / 800 : ℝ) - (1 / 16 : ℝ)) ≤
      (66657950167 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell200_denomUpper
    linarith [hpThetaJensenCell200_product_upper]
  have hi : (1 / (66657950167 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (201 / 800 : ℝ) - (1 / 16 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (66657950167 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (66657950167 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1 / 16 : ℝ) - Real.pi * Real.exp (201 / 800 : ℝ)) := by
    rw [show (1 / 16 : ℝ) - Real.pi * Real.exp (201 / 800 : ℝ) =
      -(Real.pi * Real.exp (201 / 800 : ℝ) - (1 / 16 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1 / 4 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1 / 4 : ℝ)) := by
    have h := hpThetaJensenCell200_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (66657950167 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell200_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1 / 8 : ℝ) (201 / 1600 : ℝ) ≤ (15507259307 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (201 / 800 : ℝ)) (40389307704971953 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (201 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell200_product_upper
  have hD : (33150833093 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1 / 4 : ℝ) - (201 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell200_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell200_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1 / 4 : ℝ) - (201 / 3200 : ℝ)) ≤
      (1 / (33150833093 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (33150833093 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((201 / 3200 : ℝ) - Real.pi * Real.exp (1 / 4 : ℝ)) ≤
      (2 / (33150833093 / 625000000 : ℝ) : ℝ) := by
    rw [show (201 / 3200 : ℝ) - Real.pi * Real.exp (1 / 4 : ℝ) =
      -(Real.pi * Real.exp (1 / 4 : ℝ) - (201 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (40389307704971953 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (40389307704971953 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell200_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1 / 8 : ℝ) (201 / 1600 : ℝ)) :
    (3833523963 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15507259307 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell200_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell200_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell201_leftExp :
    (321407863 / 250000000 : ℝ) ≤ Real.exp (201 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (201 / 800 : ℝ) (503941233423 / 500000000000 : ℝ)
    (321407863 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell201_rightExp :
    Real.exp (101 / 400 : ℝ) ≤ (6436197481 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (101 / 400 : ℝ) (40316873521 / 40000000000 : ℝ)
    (6436197481 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell201_denomUpper :
    Real.exp (19905850452927233 / 5000000000000000 : ℝ) ≤ (267898453279 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (19905850452927233 / 5000000000000000 : ℝ) (1132481865373
    / 1000000000000 : ℝ) (267898453279 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell201_denomLower :
    (26646486519 / 500000000 : ℝ) ≤ Real.exp (124243890142237 / 31250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (124243890142237 / 31250000000000 : ℝ) (1132291992181 /
    1000000000000 : ℝ) (26646486519 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell201_product_lower :
    (126216546392237 / 31250000000000 : ℝ) ≤ Real.pi * Real.exp (201 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell201_leftExp
    (by norm_num : (0 : ℝ) ≤ (321407863 / 250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell201_product_upper :
    Real.pi * Real.exp (101 / 400 : ℝ) ≤ (20219912952927233 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell201_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell201_endpointLower :
    (3827777663 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (201 / 1600 : ℝ) (101 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (126216546392237 / 31250000000000 : ℝ) (Real.pi * Real.exp (201 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell201_product_lower
  have hD : Real.exp (Real.pi * Real.exp (101 / 400 : ℝ) - (201 / 3200 : ℝ)) ≤
      (267898453279 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell201_denomUpper
    linarith [hpThetaJensenCell201_product_upper]
  have hi : (1 / (267898453279 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (101 / 400 : ℝ) - (201 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (267898453279 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (267898453279 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((201 / 3200 : ℝ) - Real.pi * Real.exp (101 / 400 : ℝ)) := by
    rw [show (201 / 3200 : ℝ) - Real.pi * Real.exp (101 / 400 : ℝ) =
      -(Real.pi * Real.exp (101 / 400 : ℝ) - (201 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (201 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (201 / 800 : ℝ)) := by
    have h := hpThetaJensenCell201_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (267898453279 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell201_endpointUpper :
    hpThetaJensenKernelEndpointUpper (201 / 1600 : ℝ) (101 / 800 : ℝ) ≤ (15484089531 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (101 / 400 : ℝ)) (20219912952927233 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (101 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell201_product_upper
  have hD : (26646486519 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (201 / 800 : ℝ) - (101 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell201_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell201_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (201 / 800 : ℝ) - (101 / 1600 : ℝ)) ≤
      (1 / (26646486519 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (26646486519 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((101 / 1600 : ℝ) - Real.pi * Real.exp (201 / 800 : ℝ)) ≤
      (2 / (26646486519 / 500000000 : ℝ) : ℝ) := by
    rw [show (101 / 1600 : ℝ) - Real.pi * Real.exp (201 / 800 : ℝ) =
      -(Real.pi * Real.exp (201 / 800 : ℝ) - (101 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (20219912952927233 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (20219912952927233 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell201_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (201 / 1600 : ℝ) (101 / 800 : ℝ)) :
    (3827777663 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15484089531 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell201_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell201_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell202_leftExp :
    (12872394961 / 10000000000 : ℝ) ≤ Real.exp (101 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (101 / 400 : ℝ) (125990229753 / 125000000000 : ℝ)
    (12872394961 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell202_rightExp :
    Real.exp (203 / 800 : ℝ) ≤ (12888495517 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (203 / 800 : ℝ) (50398060537 / 50000000000 : ℝ)
    (12888495517 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell202_denomUpper :
    Real.exp (39859157296738581 / 10000000000000000 : ℝ) ≤ (538345648221 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (39859157296738581 / 10000000000000000 : ℝ)
    (1132649826271 / 1000000000000 : ℝ) (538345648221 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell202_denomLower :
    (133865362167 / 2500000000 : ℝ) ≤ Real.exp (4975679753789739 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4975679753789739 / 1250000000000000 : ℝ) (283114925309 /
    250000000000 : ℝ) (133865362167 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell202_product_lower :
    (5054976628789739 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (101 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell202_leftExp
    (by norm_num : (0 : ℝ) ≤ (12872394961 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell202_product_upper :
    Real.pi * Real.exp (203 / 800 : ℝ) ≤ (40490407296738581 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell202_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell202_endpointLower :
    (7644020423 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (101 / 800 : ℝ) (203 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5054976628789739 / 1250000000000000 : ℝ) (Real.pi * Real.exp (101 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell202_product_lower
  have hD : Real.exp (Real.pi * Real.exp (203 / 800 : ℝ) - (101 / 1600 : ℝ)) ≤
      (538345648221 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell202_denomUpper
    linarith [hpThetaJensenCell202_product_upper]
  have hi : (1 / (538345648221 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (203 / 800 : ℝ) - (101 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (538345648221 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (538345648221 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((101 / 1600 : ℝ) - Real.pi * Real.exp (203 / 800 : ℝ)) := by
    rw [show (101 / 1600 : ℝ) - Real.pi * Real.exp (203 / 800 : ℝ) =
      -(Real.pi * Real.exp (203 / 800 : ℝ) - (101 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (101 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (101 / 400 : ℝ)) := by
    have h := hpThetaJensenCell202_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (538345648221 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell202_endpointUpper :
    hpThetaJensenKernelEndpointUpper (101 / 800 : ℝ) (203 / 1600 : ℝ) ≤ (15460834169 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (203 / 800 : ℝ)) (40490407296738581 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (203 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell202_product_upper
  have hD : (133865362167 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (101 / 400 : ℝ) - (203 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell202_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell202_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (101 / 400 : ℝ) - (203 / 3200 : ℝ)) ≤
      (1 / (133865362167 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (133865362167 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((203 / 3200 : ℝ) - Real.pi * Real.exp (101 / 400 : ℝ)) ≤
      (2 / (133865362167 / 2500000000 : ℝ) : ℝ) := by
    rw [show (203 / 3200 : ℝ) - Real.pi * Real.exp (101 / 400 : ℝ) =
      -(Real.pi * Real.exp (101 / 400 : ℝ) - (203 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (40490407296738581 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (40490407296738581 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell202_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (101 / 800 : ℝ) (203 / 1600 : ℝ)) :
    (7644020423 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15460834169 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell202_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell202_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell203_leftExp :
    (2577699103 / 2000000000 : ℝ) ≤ Real.exp (203 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (203 / 800 : ℝ) (1007961210739 / 1000000000000 : ℝ)
    (2577699103 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell203_rightExp :
    Real.exp (51 / 200 : ℝ) ≤ (12904616209 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (51 / 200 : ℝ) (504000292497 / 500000000000 : ℝ)
    (12904616209 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell203_denomUpper :
    Real.exp (39906676949880937 / 10000000000000000 : ℝ) ≤ (540909935951 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (39906676949880937 / 10000000000000000 : ℝ) (17700281813
    / 15625000000 : ℝ) (540909935951 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell203_denomLower :
    (269004296777 / 5000000000 : ℝ) ≤ Real.exp (996322360048997 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (996322360048997 / 250000000000000 : ℝ) (1132627658779 /
    1000000000000 : ℝ) (269004296777 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell203_product_lower :
    (1012259860048997 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (203 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell203_leftExp
    (by norm_num : (0 : ℝ) ≤ (2577699103 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell203_product_upper :
    Real.pi * Real.exp (51 / 200 : ℝ) ≤ (40541051949880937 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell203_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell203_endpointLower :
    (24423819 / 16000000 : ℝ) ≤ hpThetaTraceEndpointLower (203 / 1600 : ℝ) (51 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1012259860048997 / 250000000000000 : ℝ) (Real.pi * Real.exp (203 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell203_product_lower
  have hD : Real.exp (Real.pi * Real.exp (51 / 200 : ℝ) - (203 / 3200 : ℝ)) ≤
      (540909935951 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell203_denomUpper
    linarith [hpThetaJensenCell203_product_upper]
  have hi : (1 / (540909935951 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (51 / 200 : ℝ) - (203 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (540909935951 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (540909935951 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((203 / 3200 : ℝ) - Real.pi * Real.exp (51 / 200 : ℝ)) := by
    rw [show (203 / 3200 : ℝ) - Real.pi * Real.exp (51 / 200 : ℝ) =
      -(Real.pi * Real.exp (51 / 200 : ℝ) - (203 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (203 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (203 / 800 : ℝ)) := by
    have h := hpThetaJensenCell203_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (540909935951 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell203_endpointUpper :
    hpThetaJensenKernelEndpointUpper (203 / 1600 : ℝ) (51 / 400 : ℝ) ≤ (15437493637 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (51 / 200 : ℝ)) (40541051949880937 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (51 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell203_product_upper
  have hD : (269004296777 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (203 / 800 : ℝ) - (51 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell203_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell203_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (203 / 800 : ℝ) - (51 / 800 : ℝ)) ≤
      (1 / (269004296777 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (269004296777 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((51 / 800 : ℝ) - Real.pi * Real.exp (203 / 800 : ℝ)) ≤
      (2 / (269004296777 / 5000000000 : ℝ) : ℝ) := by
    rw [show (51 / 800 : ℝ) - Real.pi * Real.exp (203 / 800 : ℝ) =
      -(Real.pi * Real.exp (203 / 800 : ℝ) - (51 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (40541051949880937 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (40541051949880937 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell203_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (203 / 1600 : ℝ) (51 / 400 : ℝ)) :
    (24423819 / 16000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15437493637 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell203_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell203_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell204_leftExp :
    (806538513 / 625000000 : ℝ) ≤ Real.exp (51 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (51 / 200 : ℝ) (1008000584993 / 1000000000000 : ℝ)
    (806538513 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell204_rightExp :
    Real.exp (41 / 160 : ℝ) ≤ (6460378533 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (41 / 160 : ℝ) (504019980393 / 500000000000 : ℝ)
    (6460378533 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell204_denomUpper :
    Real.exp (19977129976623069 / 5000000000000000 : ℝ) ≤ (530751837 / 9765625 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (19977129976623069 / 5000000000000000 : ℝ) (113298649507
    / 100000000000 : ℝ) (530751837 / 9765625 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell204_denomLower :
    (108114255017 / 2000000000 : ℝ) ≤ Real.exp (311721984704087 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (311721984704087 / 78125000000000 : ℝ) (1132795865201 /
    1000000000000 : ℝ) (108114255017 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell204_product_lower :
    (316726867516587 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (51 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell204_leftExp
    (by norm_num : (0 : ℝ) ≤ (806538513 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell204_product_upper :
    Real.pi * Real.exp (41 / 160 : ℝ) ≤ (20295879976623069 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell204_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell204_endpointLower :
    (3810412289 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (51 / 400 : ℝ) (41 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (316726867516587 / 78125000000000 : ℝ) (Real.pi * Real.exp (51 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell204_product_lower
  have hD : Real.exp (Real.pi * Real.exp (41 / 160 : ℝ) - (51 / 800 : ℝ)) ≤
      (530751837 / 9765625 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell204_denomUpper
    linarith [hpThetaJensenCell204_product_upper]
  have hi : (1 / (530751837 / 9765625 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (41 / 160 : ℝ) - (51 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (530751837 / 9765625 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (530751837 / 9765625 : ℝ) : ℝ) ≤
      2 * Real.exp ((51 / 800 : ℝ) - Real.pi * Real.exp (41 / 160 : ℝ)) := by
    rw [show (51 / 800 : ℝ) - Real.pi * Real.exp (41 / 160 : ℝ) =
      -(Real.pi * Real.exp (41 / 160 : ℝ) - (51 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (51 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (51 / 200 : ℝ)) := by
    have h := hpThetaJensenCell204_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (530751837 / 9765625 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell204_endpointUpper :
    hpThetaJensenKernelEndpointUpper (51 / 400 : ℝ) (41 / 320 : ℝ) ≤ (15414068371 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (41 / 160 : ℝ)) (20295879976623069 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (41 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell204_product_upper
  have hD : (108114255017 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (51 / 200 : ℝ) - (41 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell204_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell204_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (51 / 200 : ℝ) - (41 / 640 : ℝ)) ≤
      (1 / (108114255017 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (108114255017 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((41 / 640 : ℝ) - Real.pi * Real.exp (51 / 200 : ℝ)) ≤
      (2 / (108114255017 / 2000000000 : ℝ) : ℝ) := by
    rw [show (41 / 640 : ℝ) - Real.pi * Real.exp (51 / 200 : ℝ) =
      -(Real.pi * Real.exp (51 / 200 : ℝ) - (41 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (20295879976623069 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (20295879976623069 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell204_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (51 / 400 : ℝ) (41 / 320 : ℝ)) :
    (3810412289 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15414068371 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell204_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell204_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell205_leftExp :
    (1615094633 / 1250000000 : ℝ) ≤ Real.exp (41 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (41 / 160 : ℝ) (201607992157 / 200000000000 : ℝ)
    (1615094633 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell205_rightExp :
    Real.exp (103 / 400 : ℝ) ≤ (1293691811 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (103 / 400 : ℝ) (252019834529 / 250000000000 : ℝ)
    (1293691811 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell205_denomUpper :
    Real.exp (4000190637594923 / 1000000000000000 : ℝ) ≤ (546085594859 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4000190637594923 / 1000000000000000 : ℝ) (566577601867 /
    500000000000 : ℝ) (546085594859 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell205_denomLower :
    (33946850243 / 625000000 : ℝ) ≤ Real.exp (624187453534467 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (624187453534467 / 156250000000000 : ℝ) (566482160437 /
    500000000000 : ℝ) (33946850243 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell205_product_lower :
    (634246047284467 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (41 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell205_leftExp
    (by norm_num : (0 : ℝ) ≤ (1615094633 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell205_product_upper :
    Real.pi * Real.exp (103 / 400 : ℝ) ≤ (4064253137594923 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell205_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell205_endpointLower :
    (1521832813 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (41 / 320 : ℝ) (103 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (634246047284467 / 156250000000000 : ℝ) (Real.pi * Real.exp (41 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell205_product_lower
  have hD : Real.exp (Real.pi * Real.exp (103 / 400 : ℝ) - (41 / 640 : ℝ)) ≤
      (546085594859 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell205_denomUpper
    linarith [hpThetaJensenCell205_product_upper]
  have hi : (1 / (546085594859 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (103 / 400 : ℝ) - (41 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (546085594859 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (546085594859 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((41 / 640 : ℝ) - Real.pi * Real.exp (103 / 400 : ℝ)) := by
    rw [show (41 / 640 : ℝ) - Real.pi * Real.exp (103 / 400 : ℝ) =
      -(Real.pi * Real.exp (103 / 400 : ℝ) - (41 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (41 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (41 / 160 : ℝ)) := by
    have h := hpThetaJensenCell205_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (546085594859 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell205_endpointUpper :
    hpThetaJensenKernelEndpointUpper (41 / 320 : ℝ) (103 / 800 : ℝ) ≤ (38476397 / 25000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (103 / 400 : ℝ)) (4064253137594923 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (103 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell205_product_upper
  have hD : (33946850243 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (41 / 160 : ℝ) - (103 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell205_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell205_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (41 / 160 : ℝ) - (103 / 1600 : ℝ)) ≤
      (1 / (33946850243 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (33946850243 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((103 / 1600 : ℝ) - Real.pi * Real.exp (41 / 160 : ℝ)) ≤
      (2 / (33946850243 / 625000000 : ℝ) : ℝ) := by
    rw [show (103 / 1600 : ℝ) - Real.pi * Real.exp (41 / 160 : ℝ) =
      -(Real.pi * Real.exp (41 / 160 : ℝ) - (103 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4064253137594923 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (4064253137594923 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell205_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (41 / 320 : ℝ) (103 / 800 : ℝ)) :
    (1521832813 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (38476397 / 25000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell205_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell205_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell206_leftExp :
    (12936918109 / 10000000000 : ℝ) ≤ Real.exp (103 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (103 / 400 : ℝ) (201615867623 / 200000000000 : ℝ)
    (12936918109 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell206_rightExp :
    Real.exp (207 / 800 : ℝ) ≤ (1295309937 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (207 / 800 : ℝ) (201623743397 / 200000000000 : ℝ)
    (1295309937 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell206_denomUpper :
    Real.exp (4004961630909641 / 1000000000000000 : ℝ) ≤ (548697190581 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4004961630909641 / 1000000000000000 : ℝ) (1133324162451
    / 1000000000000 : ℝ) (548697190581 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell206_denomLower :
    (27287184589 / 500000000 : ℝ) ≤ Real.exp (4999455429486191 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4999455429486191 / 1250000000000000 : ℝ) (113313302619 /
    100000000000 : ℝ) (27287184589 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell206_product_lower :
    (5080314804486191 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (103 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell206_leftExp
    (by norm_num : (0 : ℝ) ≤ (12936918109 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell206_product_upper :
    Real.pi * Real.exp (207 / 800 : ℝ) ≤ (4069336630909641 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell206_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell206_endpointLower :
    (15194924211 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (103 / 800 : ℝ) (207 / 1600 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5080314804486191 / 1250000000000000 : ℝ) (Real.pi * Real.exp (103 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell206_product_lower
  have hD : Real.exp (Real.pi * Real.exp (207 / 800 : ℝ) - (103 / 1600 : ℝ)) ≤
      (548697190581 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell206_denomUpper
    linarith [hpThetaJensenCell206_product_upper]
  have hi : (1 / (548697190581 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (207 / 800 : ℝ) - (103 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (548697190581 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (548697190581 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((103 / 1600 : ℝ) - Real.pi * Real.exp (207 / 800 : ℝ)) := by
    rw [show (103 / 1600 : ℝ) - Real.pi * Real.exp (207 / 800 : ℝ) =
      -(Real.pi * Real.exp (207 / 800 : ℝ) - (103 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (103 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (103 / 400 : ℝ)) := by
    have h := hpThetaJensenCell206_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (548697190581 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell206_endpointUpper :
    hpThetaJensenKernelEndpointUpper (103 / 800 : ℝ) (207 / 1600 : ℝ) ≤ (3841741341 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (207 / 800 : ℝ)) (4069336630909641 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (207 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell206_product_upper
  have hD : (27287184589 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (103 / 400 : ℝ) - (207 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell206_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell206_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (103 / 400 : ℝ) - (207 / 3200 : ℝ)) ≤
      (1 / (27287184589 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (27287184589 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((207 / 3200 : ℝ) - Real.pi * Real.exp (103 / 400 : ℝ)) ≤
      (2 / (27287184589 / 500000000 : ℝ) : ℝ) := by
    rw [show (207 / 3200 : ℝ) - Real.pi * Real.exp (103 / 400 : ℝ) =
      -(Real.pi * Real.exp (103 / 400 : ℝ) - (207 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4069336630909641 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (4069336630909641 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell206_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (103 / 800 : ℝ) (207 / 1600 : ℝ)) :
    (15194924211 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3841741341 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell206_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell206_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell207_leftExp :
    (1619137421 / 1250000000 : ℝ) ≤ Real.exp (207 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (207 / 800 : ℝ) (126014839623 / 125000000000 : ℝ)
    (1619137421 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell207_rightExp :
    Real.exp (13 / 50 : ℝ) ≤ (12969300867 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (13 / 50 : ℝ) (1008158097391 / 1000000000000 : ℝ)
    (12969300867 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell207_denomUpper :
    Real.exp (40097389818661131 / 10000000000000000 : ℝ) ≤ (551324781097 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (40097389818661131 / 10000000000000000 : ℝ)
    (1133493371559 / 1000000000000 : ℝ) (551324781097 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell207_denomLower :
    (137088412833 / 2500000000 : ℝ) ≤ Real.exp (625677396089279 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (625677396089279 / 156250000000000 : ℝ) (283325495383 /
    250000000000 : ℝ) (137088412833 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell207_product_lower :
    (635833646089279 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (207 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell207_leftExp
    (by norm_num : (0 : ℝ) ≤ (1619137421 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell207_product_upper :
    Real.pi * Real.exp (13 / 50 : ℝ) ≤ (40744264818661131 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell207_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell207_endpointLower :
    (3792859463 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (207 / 1600 : ℝ) (13 / 100 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (635833646089279 / 156250000000000 : ℝ) (Real.pi * Real.exp (207 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell207_product_lower
  have hD : Real.exp (Real.pi * Real.exp (13 / 50 : ℝ) - (207 / 3200 : ℝ)) ≤
      (551324781097 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell207_denomUpper
    linarith [hpThetaJensenCell207_product_upper]
  have hi : (1 / (551324781097 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (13 / 50 : ℝ) - (207 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (551324781097 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (551324781097 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((207 / 3200 : ℝ) - Real.pi * Real.exp (13 / 50 : ℝ)) := by
    rw [show (207 / 3200 : ℝ) - Real.pi * Real.exp (13 / 50 : ℝ) =
      -(Real.pi * Real.exp (13 / 50 : ℝ) - (207 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (207 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (207 / 800 : ℝ)) := by
    have h := hpThetaJensenCell207_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (551324781097 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell207_endpointUpper :
    hpThetaJensenKernelEndpointUpper (207 / 1600 : ℝ) (13 / 100 : ℝ) ≤ (3068657697 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (13 / 50 : ℝ)) (40744264818661131 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (13 / 100 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell207_product_upper
  have hD : (137088412833 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (207 / 800 : ℝ) - (13 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell207_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell207_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (207 / 800 : ℝ) - (13 / 200 : ℝ)) ≤
      (1 / (137088412833 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (137088412833 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((13 / 200 : ℝ) - Real.pi * Real.exp (207 / 800 : ℝ)) ≤
      (2 / (137088412833 / 2500000000 : ℝ) : ℝ) := by
    rw [show (13 / 200 : ℝ) - Real.pi * Real.exp (207 / 800 : ℝ) =
      -(Real.pi * Real.exp (207 / 800 : ℝ) - (13 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (40744264818661131 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (40744264818661131 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell207_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (207 / 1600 : ℝ) (13 / 100 : ℝ)) :
    (3792859463 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3068657697 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell207_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell207_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell208_leftExp :
    (6484650433 / 5000000000 : ℝ) ≤ Real.exp (13 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (13 / 50 : ℝ) (100815809739 / 100000000000 : ℝ)
    (6484650433 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell208_rightExp :
    Real.exp (209 / 800 : ℝ) ≤ (1298552263 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (209 / 800 : ℝ) (126024684917 / 125000000000 : ℝ)
    (1298552263 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell208_denomUpper :
    Real.exp (4014522699574959 / 1000000000000000 : ℝ) ≤ (276984240767 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4014522699574959 / 1000000000000000 : ℝ) (226732566297 /
    200000000000 : ℝ) (276984240767 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell208_denomLower :
    (550979595993 / 10000000000 : ℝ) ≤ Real.exp (2505695427888667 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2505695427888667 / 625000000000000 : ℝ) (566735593641 /
    500000000000 : ℝ) (550979595993 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell208_product_lower :
    (2546515740388667 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (13 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell208_leftExp
    (by norm_num : (0 : ℝ) ≤ (6484650433 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell208_product_upper :
    Real.pi * Real.exp (209 / 800 : ℝ) ≤ (4079522699574959 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell208_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell208_endpointLower :
    (3029573893 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (13 / 100 : ℝ) (209 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2546515740388667 / 625000000000000 : ℝ) (Real.pi * Real.exp (13 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell208_product_lower
  have hD : Real.exp (Real.pi * Real.exp (209 / 800 : ℝ) - (13 / 200 : ℝ)) ≤
      (276984240767 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell208_denomUpper
    linarith [hpThetaJensenCell208_product_upper]
  have hi : (1 / (276984240767 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (209 / 800 : ℝ) - (13 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (276984240767 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (276984240767 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((13 / 200 : ℝ) - Real.pi * Real.exp (209 / 800 : ℝ)) := by
    rw [show (13 / 200 : ℝ) - Real.pi * Real.exp (209 / 800 : ℝ) =
      -(Real.pi * Real.exp (209 / 800 : ℝ) - (13 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (13 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (13 / 50 : ℝ)) := by
    have h := hpThetaJensenCell208_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (276984240767 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell208_endpointUpper :
    hpThetaJensenKernelEndpointUpper (13 / 100 : ℝ) (209 / 1600 : ℝ) ≤ (3829882153 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (209 / 800 : ℝ)) (4079522699574959 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (209 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell208_product_upper
  have hD : (550979595993 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (13 / 50 : ℝ) - (209 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell208_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell208_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (13 / 50 : ℝ) - (209 / 3200 : ℝ)) ≤
      (1 / (550979595993 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (550979595993 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((209 / 3200 : ℝ) - Real.pi * Real.exp (13 / 50 : ℝ)) ≤
      (2 / (550979595993 / 10000000000 : ℝ) : ℝ) := by
    rw [show (209 / 3200 : ℝ) - Real.pi * Real.exp (13 / 50 : ℝ) =
      -(Real.pi * Real.exp (13 / 50 : ℝ) - (209 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4079522699574959 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (4079522699574959 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell208_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (13 / 100 : ℝ) (209 / 1600 : ℝ)) :
    (3029573893 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3829882153 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell208_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell208_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell209_leftExp :
    (12985522629 / 10000000000 : ℝ) ≤ Real.exp (209 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (209 / 800 : ℝ) (201639495867 / 200000000000 : ℝ)
    (12985522629 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell209_rightExp :
    Real.exp (21 / 80 : ℝ) ≤ (6500882341 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21 / 80 : ℝ) (1008236862819 / 1000000000000 : ℝ)
    (6500882341 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell209_denomUpper :
    Real.exp (20096563956309213 / 5000000000000000 : ℝ) ≤ (55662840691 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (20096563956309213 / 5000000000000000 : ℝ) (113383254259
    / 100000000000 : ℝ) (55662840691 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell209_denomLower :
    (553621640309 / 10000000000 : ℝ) ≤ Real.exp (5017370500885671 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5017370500885671 / 1250000000000000 : ℝ) (566820321917 /
    500000000000 : ℝ) (553621640309 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell209_product_lower :
    (5099401750885671 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (209 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell209_leftExp
    (by norm_num : (0 : ℝ) ≤ (12985522629 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell209_product_upper :
    Real.pi * Real.exp (21 / 80 : ℝ) ≤ (20423126456309213 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell209_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell209_endpointLower :
    (30248439 / 20000000 : ℝ) ≤ hpThetaTraceEndpointLower (209 / 1600 : ℝ) (21 / 160 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5099401750885671 / 1250000000000000 : ℝ) (Real.pi * Real.exp (209 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell209_product_lower
  have hD : Real.exp (Real.pi * Real.exp (21 / 80 : ℝ) - (209 / 3200 : ℝ)) ≤
      (55662840691 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell209_denomUpper
    linarith [hpThetaJensenCell209_product_upper]
  have hi : (1 / (55662840691 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (21 / 80 : ℝ) - (209 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (55662840691 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (55662840691 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((209 / 3200 : ℝ) - Real.pi * Real.exp (21 / 80 : ℝ)) := by
    rw [show (209 / 3200 : ℝ) - Real.pi * Real.exp (21 / 80 : ℝ) =
      -(Real.pi * Real.exp (21 / 80 : ℝ) - (209 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (209 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (209 / 800 : ℝ)) := by
    have h := hpThetaJensenCell209_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (55662840691 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell209_endpointUpper :
    hpThetaJensenKernelEndpointUpper (209 / 1600 : ℝ) (21 / 160 : ℝ) ≤ (15295686171 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (21 / 80 : ℝ)) (20423126456309213 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (21 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell209_product_upper
  have hD : (553621640309 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (209 / 800 : ℝ) - (21 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell209_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell209_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (209 / 800 : ℝ) - (21 / 320 : ℝ)) ≤
      (1 / (553621640309 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (553621640309 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((21 / 320 : ℝ) - Real.pi * Real.exp (209 / 800 : ℝ)) ≤
      (2 / (553621640309 / 10000000000 : ℝ) : ℝ) := by
    rw [show (21 / 320 : ℝ) - Real.pi * Real.exp (209 / 800 : ℝ) =
      -(Real.pi * Real.exp (209 / 800 : ℝ) - (21 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (20423126456309213 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (20423126456309213 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell209_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (209 / 1600 : ℝ) (21 / 160 : ℝ)) :
    (30248439 / 20000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15295686171 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell209_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell209_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell210_leftExp :
    (13001764681 / 10000000000 : ℝ) ≤ Real.exp (21 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (21 / 80 : ℝ) (504118431409 / 500000000000 : ℝ)
    (13001764681 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell210_rightExp :
    Real.exp (211 / 800 : ℝ) ≤ (260360541 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (211 / 800 : ℝ) (1008276247841 / 1000000000000 : ℝ)
    (260360541 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell210_denomUpper :
    Real.exp (804821853081813 / 200000000000000 : ℝ) ≤ (111860934773 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (804821853081813 / 200000000000000 : ℝ) (3543757829 /
    3125000000 : ℝ) (111860934773 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell210_denomLower :
    (111255979879 / 2000000000 : ℝ) ≤ Real.exp (5023358113464019 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5023358113464019 / 1250000000000000 : ℝ) (28345258789 /
    25000000000 : ℝ) (111255979879 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell210_product_lower :
    (5105779988464019 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (21 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell210_leftExp
    (by norm_num : (0 : ℝ) ≤ (13001764681 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell210_product_upper :
    Real.pi * Real.exp (211 / 800 : ℝ) ≤ (817946853081813 / 200000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell210_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell210_endpointLower :
    (7550244189 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (21 / 160 : ℝ) (211 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5105779988464019 / 1250000000000000 : ℝ) (Real.pi * Real.exp (21 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell210_product_lower
  have hD : Real.exp (Real.pi * Real.exp (211 / 800 : ℝ) - (21 / 320 : ℝ)) ≤
      (111860934773 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell210_denomUpper
    linarith [hpThetaJensenCell210_product_upper]
  have hi : (1 / (111860934773 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (211 / 800 : ℝ) - (21 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (111860934773 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (111860934773 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((21 / 320 : ℝ) - Real.pi * Real.exp (211 / 800 : ℝ)) := by
    rw [show (21 / 320 : ℝ) - Real.pi * Real.exp (211 / 800 : ℝ) =
      -(Real.pi * Real.exp (211 / 800 : ℝ) - (21 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (21 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (21 / 80 : ℝ)) := by
    have h := hpThetaJensenCell210_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (111860934773 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell210_endpointUpper :
    hpThetaJensenKernelEndpointUpper (21 / 160 : ℝ) (211 / 1600 : ℝ) ≤ (15271761611 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (211 / 800 : ℝ)) (817946853081813 / 200000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (211 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell210_product_upper
  have hD : (111255979879 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (21 / 80 : ℝ) - (211 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell210_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell210_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (21 / 80 : ℝ) - (211 / 3200 : ℝ)) ≤
      (1 / (111255979879 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (111255979879 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((211 / 3200 : ℝ) - Real.pi * Real.exp (21 / 80 : ℝ)) ≤
      (2 / (111255979879 / 2000000000 : ℝ) : ℝ) := by
    rw [show (211 / 3200 : ℝ) - Real.pi * Real.exp (21 / 80 : ℝ) =
      -(Real.pi * Real.exp (21 / 80 : ℝ) - (211 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (817946853081813 / 200000000000000 : ℝ) ^ 2 - 6 *
      (817946853081813 / 200000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell210_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (21 / 160 : ℝ) (211 / 1600 : ℝ)) :
    (7550244189 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15271761611 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell210_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell210_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell211_leftExp :
    (13018027049 / 10000000000 : ℝ) ≤ Real.exp (211 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (211 / 800 : ℝ) (6301726549 / 6250000000 : ℝ)
    (13018027049 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell211_rightExp :
    Real.exp (53 / 200 : ℝ) ≤ (6517154879 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (53 / 200 : ℝ) (1008315634401 / 1000000000000 : ℝ)
    (6517154879 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell211_denomUpper :
    Real.exp (20144560647782247 / 5000000000000000 : ℝ) ≤ (280998699721 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (20144560647782247 / 5000000000000000 : ℝ) (1134172719927
    / 1000000000000 : ℝ) (280998699721 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell211_denomLower :
    (558954489821 / 10000000000 : ℝ) ≤ Real.exp (5029353704115251 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5029353704115251 / 1250000000000000 : ℝ) (566990155433 /
    500000000000 : ℝ) (558954489821 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell211_product_lower :
    (5112166204115251 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (211 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell211_leftExp
    (by norm_num : (0 : ℝ) ≤ (13018027049 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell211_product_upper :
    Real.pi * Real.exp (53 / 200 : ℝ) ≤ (20474248147782247 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell211_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell211_endpointLower :
    (15076676549 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (211 / 1600 : ℝ) (53 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5112166204115251 / 1250000000000000 : ℝ) (Real.pi * Real.exp (211 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell211_product_lower
  have hD : Real.exp (Real.pi * Real.exp (53 / 200 : ℝ) - (211 / 3200 : ℝ)) ≤
      (280998699721 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell211_denomUpper
    linarith [hpThetaJensenCell211_product_upper]
  have hi : (1 / (280998699721 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (53 / 200 : ℝ) - (211 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (280998699721 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (280998699721 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((211 / 3200 : ℝ) - Real.pi * Real.exp (53 / 200 : ℝ)) := by
    rw [show (211 / 3200 : ℝ) - Real.pi * Real.exp (53 / 200 : ℝ) =
      -(Real.pi * Real.exp (53 / 200 : ℝ) - (211 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (211 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (211 / 800 : ℝ)) := by
    have h := hpThetaJensenCell211_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (280998699721 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell211_endpointUpper :
    hpThetaJensenKernelEndpointUpper (211 / 1600 : ℝ) (53 / 400 : ℝ) ≤ (95298471 / 62500000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (53 / 200 : ℝ)) (20474248147782247 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (53 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell211_product_upper
  have hD : (558954489821 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (211 / 800 : ℝ) - (53 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell211_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell211_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (211 / 800 : ℝ) - (53 / 800 : ℝ)) ≤
      (1 / (558954489821 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (558954489821 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((53 / 800 : ℝ) - Real.pi * Real.exp (211 / 800 : ℝ)) ≤
      (2 / (558954489821 / 10000000000 : ℝ) : ℝ) := by
    rw [show (53 / 800 : ℝ) - Real.pi * Real.exp (211 / 800 : ℝ) =
      -(Real.pi * Real.exp (211 / 800 : ℝ) - (53 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (20474248147782247 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (20474248147782247 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell211_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (211 / 1600 : ℝ) (53 / 400 : ℝ)) :
    (15076676549 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (95298471 / 62500000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell211_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell211_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell212_leftExp :
    (13034309757 / 10000000000 : ℝ) ≤ Real.exp (53 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (53 / 200 : ℝ) (1260394543 / 1250000000 : ℝ) (13034309757
    / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell212_rightExp :
    Real.exp (213 / 800 : ℝ) ≤ (13050612833 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (213 / 800 : ℝ) (403342009 / 400000000 : ℝ)
    (13050612833 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell212_denomUpper :
    Real.exp (40337213921862969 / 10000000000000000 : ℝ) ≤ (564706702189 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (40337213921862969 / 10000000000000000 : ℝ)
    (1134343186939 / 1000000000000 : ℝ) (564706702189 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell212_denomLower :
    (561645528553 / 10000000000 : ℝ) ≤ Real.exp (5035357282264143 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5035357282264143 / 1250000000000000 : ℝ) (283537630531 /
    250000000000 : ℝ) (561645528553 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell212_product_lower :
    (5118560407264143 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (53 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell212_leftExp
    (by norm_num : (0 : ℝ) ≤ (13034309757 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell212_product_upper :
    Real.pi * Real.exp (213 / 800 : ℝ) ≤ (40999713921862969 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell212_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell212_endpointLower :
    (3763196109 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (53 / 400 : ℝ) (213 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5118560407264143 / 1250000000000000 : ℝ) (Real.pi * Real.exp (53 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell212_product_lower
  have hD : Real.exp (Real.pi * Real.exp (213 / 800 : ℝ) - (53 / 800 : ℝ)) ≤
      (564706702189 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell212_denomUpper
    linarith [hpThetaJensenCell212_product_upper]
  have hi : (1 / (564706702189 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (213 / 800 : ℝ) - (53 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (564706702189 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (564706702189 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((53 / 800 : ℝ) - Real.pi * Real.exp (213 / 800 : ℝ)) := by
    rw [show (53 / 800 : ℝ) - Real.pi * Real.exp (213 / 800 : ℝ) =
      -(Real.pi * Real.exp (213 / 800 : ℝ) - (53 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (53 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (53 / 200 : ℝ)) := by
    have h := hpThetaJensenCell212_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (564706702189 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell212_endpointUpper :
    hpThetaJensenKernelEndpointUpper (53 / 400 : ℝ) (213 / 1600 : ℝ) ≤ (15223667869 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (213 / 800 : ℝ)) (40999713921862969 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (213 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell212_product_upper
  have hD : (561645528553 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (53 / 200 : ℝ) - (213 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell212_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell212_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (53 / 200 : ℝ) - (213 / 3200 : ℝ)) ≤
      (1 / (561645528553 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (561645528553 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((213 / 3200 : ℝ) - Real.pi * Real.exp (53 / 200 : ℝ)) ≤
      (2 / (561645528553 / 10000000000 : ℝ) : ℝ) := by
    rw [show (213 / 3200 : ℝ) - Real.pi * Real.exp (53 / 200 : ℝ) =
      -(Real.pi * Real.exp (53 / 200 : ℝ) - (213 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (40999713921862969 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (40999713921862969 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell212_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (53 / 400 : ℝ) (213 / 1600 : ℝ)) :
    (3763196109 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15223667869 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell212_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell212_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell213_leftExp :
    (407831651 / 312500000 : ℝ) ≤ Real.exp (213 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (213 / 800 : ℝ) (1008355022499 / 1000000000000 : ℝ)
    (407831651 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell213_rightExp :
    Real.exp (107 / 400 : ℝ) ≤ (13066936299 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (107 / 400 : ℝ) (1008394412137 / 1000000000000 : ℝ)
    (13066936299 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell213_denomUpper :
    Real.exp (40385370608384307 / 10000000000000000 : ℝ) ≤ (567432701047 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (40385370608384307 / 10000000000000000 : ℝ)
    (1134513906689 / 1000000000000 : ℝ) (567432701047 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell213_denomLower :
    (564353134067 / 10000000000 : ℝ) ≤ Real.exp (157542776828549 / 39062500000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (157542776828549 / 39062500000000 : ℝ) (567160492871 /
    500000000000 : ℝ) (564353134067 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell213_product_lower :
    (160155081516049 / 39062500000000 : ℝ) ≤ Real.pi * Real.exp (213 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell213_leftExp
    (by norm_num : (0 : ℝ) ≤ (407831651 / 312500000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell213_product_upper :
    Real.pi * Real.exp (107 / 400 : ℝ) ≤ (41050995608384307 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell213_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell213_endpointLower :
    (3757203123 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (213 / 1600 : ℝ) (107 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (160155081516049 / 39062500000000 : ℝ) (Real.pi * Real.exp (213 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell213_product_lower
  have hD : Real.exp (Real.pi * Real.exp (107 / 400 : ℝ) - (213 / 3200 : ℝ)) ≤
      (567432701047 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell213_denomUpper
    linarith [hpThetaJensenCell213_product_upper]
  have hi : (1 / (567432701047 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (107 / 400 : ℝ) - (213 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (567432701047 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (567432701047 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((213 / 3200 : ℝ) - Real.pi * Real.exp (107 / 400 : ℝ)) := by
    rw [show (213 / 3200 : ℝ) - Real.pi * Real.exp (107 / 400 : ℝ) =
      -(Real.pi * Real.exp (107 / 400 : ℝ) - (213 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (213 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (213 / 800 : ℝ)) := by
    have h := hpThetaJensenCell213_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (567432701047 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell213_endpointUpper :
    hpThetaJensenKernelEndpointUpper (213 / 1600 : ℝ) (107 / 800 : ℝ) ≤ (949968723 / 625000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (107 / 400 : ℝ)) (41050995608384307 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (107 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell213_product_upper
  have hD : (564353134067 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (213 / 800 : ℝ) - (107 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell213_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell213_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (213 / 800 : ℝ) - (107 / 1600 : ℝ)) ≤
      (1 / (564353134067 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (564353134067 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((107 / 1600 : ℝ) - Real.pi * Real.exp (213 / 800 : ℝ)) ≤
      (2 / (564353134067 / 10000000000 : ℝ) : ℝ) := by
    rw [show (107 / 1600 : ℝ) - Real.pi * Real.exp (213 / 800 : ℝ) =
      -(Real.pi * Real.exp (213 / 800 : ℝ) - (107 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (41050995608384307 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (41050995608384307 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell213_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (213 / 1600 : ℝ) (107 / 800 : ℝ)) :
    (3757203123 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (949968723 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell213_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell213_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell214_leftExp :
    (6533468149 / 5000000000 : ℝ) ≤ Real.exp (107 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (107 / 400 : ℝ) (126049301517 / 125000000000 : ℝ)
    (6533468149 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell214_rightExp :
    Real.exp (43 / 160 : ℝ) ≤ (6541640091 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (43 / 160 : ℝ) (1008433803313 / 1000000000000 : ℝ)
    (6541640091 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell214_denomUpper :
    Real.exp (20216795718404963 / 5000000000000000 : ℝ) ≤ (285087758133 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (20216795718404963 / 5000000000000000 : ℝ) (283671219893
    / 250000000000 : ℝ) (285087758133 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell214_denomLower :
    (567077425213 / 10000000000 : ℝ) ≤ Real.exp (2523694221144151 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2523694221144151 / 625000000000000 : ℝ) (283622925523 /
    250000000000 : ℝ) (567077425213 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell214_product_lower :
    (2565686408644151 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (107 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell214_leftExp
    (by norm_num : (0 : ℝ) ≤ (6533468149 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell214_product_upper :
    Real.pi * Real.exp (43 / 160 : ℝ) ≤ (20551170718404963 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell214_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell214_endpointLower :
    (3751190287 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (107 / 800 : ℝ) (43 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2565686408644151 / 625000000000000 : ℝ) (Real.pi * Real.exp (107 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell214_product_lower
  have hD : Real.exp (Real.pi * Real.exp (43 / 160 : ℝ) - (107 / 1600 : ℝ)) ≤
      (285087758133 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell214_denomUpper
    linarith [hpThetaJensenCell214_product_upper]
  have hi : (1 / (285087758133 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (43 / 160 : ℝ) - (107 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (285087758133 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (285087758133 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((107 / 1600 : ℝ) - Real.pi * Real.exp (43 / 160 : ℝ)) := by
    rw [show (107 / 1600 : ℝ) - Real.pi * Real.exp (43 / 160 : ℝ) =
      -(Real.pi * Real.exp (43 / 160 : ℝ) - (107 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (107 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (107 / 400 : ℝ)) := by
    have h := hpThetaJensenCell214_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (285087758133 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell214_endpointUpper :
    hpThetaJensenKernelEndpointUpper (107 / 800 : ℝ) (43 / 320 : ℝ) ≤ (15175250907 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (43 / 160 : ℝ)) (20551170718404963 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (43 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell214_product_upper
  have hD : (567077425213 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (107 / 400 : ℝ) - (43 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell214_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell214_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (107 / 400 : ℝ) - (43 / 640 : ℝ)) ≤
      (1 / (567077425213 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (567077425213 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((43 / 640 : ℝ) - Real.pi * Real.exp (107 / 400 : ℝ)) ≤
      (2 / (567077425213 / 10000000000 : ℝ) : ℝ) := by
    rw [show (43 / 640 : ℝ) - Real.pi * Real.exp (107 / 400 : ℝ) =
      -(Real.pi * Real.exp (107 / 400 : ℝ) - (43 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (20551170718404963 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (20551170718404963 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell214_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (107 / 800 : ℝ) (43 / 320 : ℝ)) :
    (3751190287 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15175250907 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell214_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell214_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell215_leftExp :
    (13083280181 / 10000000000 : ℝ) ≤ Real.exp (43 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (43 / 160 : ℝ) (63027112707 / 62500000000 : ℝ)
    (13083280181 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell215_rightExp :
    Real.exp (27 / 100 : ℝ) ≤ (3274911127 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (27 / 100 : ℝ) (252118299007 / 250000000000 : ℝ)
    (3274911127 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell215_denomUpper :
    Real.exp (10120469122205311 / 2500000000000000 : ℝ) ≤ (57293526909 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (10120469122205311 / 2500000000000000 : ℝ) (226971221197
    / 200000000000 : ℝ) (57293526909 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell215_denomLower :
    (569818522197 / 10000000000 : ℝ) ≤ Real.exp (5053416043798519 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5053416043798519 / 1250000000000000 : ℝ) (1134662671571
    / 1000000000000 : ℝ) (569818522197 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell215_product_lower :
    (5137791043798519 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (43 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell215_leftExp
    (by norm_num : (0 : ℝ) ≤ (13083280181 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell215_product_upper :
    Real.pi * Real.exp (27 / 100 : ℝ) ≤ (10288437872205311 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell215_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell215_endpointLower :
    (2996126169 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (43 / 320 : ℝ) (27 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5137791043798519 / 1250000000000000 : ℝ) (Real.pi * Real.exp (43 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell215_product_lower
  have hD : Real.exp (Real.pi * Real.exp (27 / 100 : ℝ) - (43 / 640 : ℝ)) ≤
      (57293526909 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell215_denomUpper
    linarith [hpThetaJensenCell215_product_upper]
  have hi : (1 / (57293526909 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (27 / 100 : ℝ) - (43 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (57293526909 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (57293526909 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((43 / 640 : ℝ) - Real.pi * Real.exp (27 / 100 : ℝ)) := by
    rw [show (43 / 640 : ℝ) - Real.pi * Real.exp (27 / 100 : ℝ) =
      -(Real.pi * Real.exp (27 / 100 : ℝ) - (43 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (43 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (43 / 160 : ℝ)) := by
    have h := hpThetaJensenCell215_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (57293526909 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell215_endpointUpper :
    hpThetaJensenKernelEndpointUpper (43 / 320 : ℝ) (27 / 200 : ℝ) ≤ (15150922329 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (27 / 100 : ℝ)) (10288437872205311 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (27 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell215_product_upper
  have hD : (569818522197 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (43 / 160 : ℝ) - (27 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell215_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell215_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (43 / 160 : ℝ) - (27 / 400 : ℝ)) ≤
      (1 / (569818522197 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (569818522197 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((27 / 400 : ℝ) - Real.pi * Real.exp (43 / 160 : ℝ)) ≤
      (2 / (569818522197 / 10000000000 : ℝ) : ℝ) := by
    rw [show (27 / 400 : ℝ) - Real.pi * Real.exp (43 / 160 : ℝ) =
      -(Real.pi * Real.exp (43 / 160 : ℝ) - (27 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (10288437872205311 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (10288437872205311 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell215_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (43 / 320 : ℝ) (27 / 200 : ℝ)) :
    (2996126169 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15150922329 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell215_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell215_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell216_leftExp :
    (13099644507 / 10000000000 : ℝ) ≤ Real.exp (27 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (27 / 100 : ℝ) (1008473196027 / 1000000000000 : ℝ)
    (13099644507 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell216_rightExp :
    Real.exp (217 / 800 : ℝ) ≤ (6558014651 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (217 / 800 : ℝ) (504256295141 / 500000000000 : ℝ)
    (6558014651 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell216_denomUpper :
    Real.exp (20265112921479043 / 5000000000000000 : ℝ) ≤ (143928020387 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (20265112921479043 / 5000000000000000 : ℝ) (1135027586313
    / 1000000000000 : ℝ) (143928020387 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell216_denomLower :
    (572576546173 / 10000000000 : ℝ) ≤ Real.exp (5059451673254393 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5059451673254393 / 1250000000000000 : ℝ) (45393355783 /
    40000000000 : ℝ) (572576546173 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell216_product_lower :
    (5144217298254393 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (27 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell216_leftExp
    (by norm_num : (0 : ℝ) ≤ (13099644507 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell216_product_upper :
    Real.pi * Real.exp (217 / 800 : ℝ) ≤ (20602612921479043 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell216_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell216_endpointLower :
    (14956422029 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (27 / 200 : ℝ) (217 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5144217298254393 / 1250000000000000 : ℝ) (Real.pi * Real.exp (27 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell216_product_lower
  have hD : Real.exp (Real.pi * Real.exp (217 / 800 : ℝ) - (27 / 400 : ℝ)) ≤
      (143928020387 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell216_denomUpper
    linarith [hpThetaJensenCell216_product_upper]
  have hi : (1 / (143928020387 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (217 / 800 : ℝ) - (27 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (143928020387 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (143928020387 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((27 / 400 : ℝ) - Real.pi * Real.exp (217 / 800 : ℝ)) := by
    rw [show (27 / 400 : ℝ) - Real.pi * Real.exp (217 / 800 : ℝ) =
      -(Real.pi * Real.exp (217 / 800 : ℝ) - (27 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (27 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (27 / 100 : ℝ)) := by
    have h := hpThetaJensenCell216_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (143928020387 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell216_endpointUpper :
    hpThetaJensenKernelEndpointUpper (27 / 200 : ℝ) (217 / 1600 : ℝ) ≤ (605060571 / 400000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (217 / 800 : ℝ)) (20602612921479043 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (217 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell216_product_upper
  have hD : (572576546173 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (27 / 100 : ℝ) - (217 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell216_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell216_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (27 / 100 : ℝ) - (217 / 3200 : ℝ)) ≤
      (1 / (572576546173 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (572576546173 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((217 / 3200 : ℝ) - Real.pi * Real.exp (27 / 100 : ℝ)) ≤
      (2 / (572576546173 / 10000000000 : ℝ) : ℝ) := by
    rw [show (217 / 3200 : ℝ) - Real.pi * Real.exp (27 / 100 : ℝ) =
      -(Real.pi * Real.exp (27 / 100 : ℝ) - (217 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (20602612921479043 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (20602612921479043 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell216_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (27 / 200 : ℝ) (217 / 1600 : ℝ)) :
    (14956422029 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (605060571 / 400000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell216_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell216_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell217_leftExp :
    (13116029301 / 10000000000 : ℝ) ≤ Real.exp (217 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (217 / 800 : ℝ) (1008512590281 / 1000000000000 : ℝ)
    (13116029301 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell217_rightExp :
    Real.exp (109 / 400 : ℝ) ≤ (1313243459 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (109 / 400 : ℝ) (504275993037 / 500000000000 : ℝ)
    (1313243459 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell217_denomUpper :
    Real.exp (4057863958090187 / 1000000000000000 : ℝ) ≤ (578506076861 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4057863958090187 / 1000000000000000 : ℝ) (567599660477 /
    500000000000 : ℝ) (578506076861 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell217_denomLower :
    (143837904773 / 2500000000 : ℝ) ≤ Real.exp (5065495340473399 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5065495340473399 / 1250000000000000 : ℝ) (1135005371489
    / 1000000000000 : ℝ) (143837904773 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell217_product_lower :
    (5150651590473399 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (217 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell217_leftExp
    (by norm_num : (0 : ℝ) ≤ (13116029301 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell217_product_upper :
    Real.pi * Real.exp (109 / 400 : ℝ) ≤ (4125676458090187 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell217_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell217_endpointLower :
    (7466067569 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (217 / 1600 : ℝ) (109 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5150651590473399 / 1250000000000000 : ℝ) (Real.pi * Real.exp (217 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell217_product_lower
  have hD : Real.exp (Real.pi * Real.exp (109 / 400 : ℝ) - (217 / 3200 : ℝ)) ≤
      (578506076861 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell217_denomUpper
    linarith [hpThetaJensenCell217_product_upper]
  have hi : (1 / (578506076861 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (109 / 400 : ℝ) - (217 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (578506076861 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (578506076861 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((217 / 3200 : ℝ) - Real.pi * Real.exp (109 / 400 : ℝ)) := by
    rw [show (217 / 3200 : ℝ) - Real.pi * Real.exp (109 / 400 : ℝ) =
      -(Real.pi * Real.exp (109 / 400 : ℝ) - (217 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (217 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (217 / 800 : ℝ)) := by
    have h := hpThetaJensenCell217_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (578506076861 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell217_endpointUpper :
    hpThetaJensenKernelEndpointUpper (217 / 1600 : ℝ) (109 / 800 : ℝ) ≤ (3020405439 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (109 / 400 : ℝ)) (4125676458090187 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (109 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell217_product_upper
  have hD : (143837904773 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (217 / 800 : ℝ) - (109 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell217_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell217_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (217 / 800 : ℝ) - (109 / 1600 : ℝ)) ≤
      (1 / (143837904773 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (143837904773 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((109 / 1600 : ℝ) - Real.pi * Real.exp (217 / 800 : ℝ)) ≤
      (2 / (143837904773 / 2500000000 : ℝ) : ℝ) := by
    rw [show (109 / 1600 : ℝ) - Real.pi * Real.exp (217 / 800 : ℝ) =
      -(Real.pi * Real.exp (217 / 800 : ℝ) - (109 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4125676458090187 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (4125676458090187 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell217_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (217 / 1600 : ℝ) (109 / 800 : ℝ)) :
    (7466067569 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3020405439 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell217_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell217_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell218_leftExp :
    (3283108647 / 2500000000 : ℝ) ≤ Real.exp (109 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (109 / 400 : ℝ) (1008551986073 / 1000000000000 : ℝ)
    (3283108647 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell218_rightExp :
    Real.exp (219 / 800 : ℝ) ≤ (13148860397 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (219 / 800 : ℝ) (504295691703 / 500000000000 : ℝ)
    (13148860397 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell218_denomUpper :
    Real.exp (40627117781192421 / 10000000000000000 : ℝ) ≤ (145329344761 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (40627117781192421 / 10000000000000000 : ℝ) (567685655147
    / 500000000000 : ℝ) (145329344761 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell218_denomLower :
    (289071931951 / 5000000000 : ℝ) ≤ Real.exp (1267886763818253 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1267886763818253 / 312500000000000 : ℝ) (1135177102699 /
    1000000000000 : ℝ) (289071931951 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell218_product_lower :
    (1289273482568253 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (109 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell218_leftExp
    (by norm_num : (0 : ℝ) ≤ (3283108647 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell218_product_upper :
    Real.pi * Real.exp (219 / 800 : ℝ) ≤ (41308367781192421 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell218_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell218_endpointLower :
    (7453885309 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (109 / 800 : ℝ) (219 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1289273482568253 / 312500000000000 : ℝ) (Real.pi * Real.exp (109 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell218_product_lower
  have hD : Real.exp (Real.pi * Real.exp (219 / 800 : ℝ) - (109 / 1600 : ℝ)) ≤
      (145329344761 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell218_denomUpper
    linarith [hpThetaJensenCell218_product_upper]
  have hi : (1 / (145329344761 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (219 / 800 : ℝ) - (109 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (145329344761 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (145329344761 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((109 / 1600 : ℝ) - Real.pi * Real.exp (219 / 800 : ℝ)) := by
    rw [show (109 / 1600 : ℝ) - Real.pi * Real.exp (219 / 800 : ℝ) =
      -(Real.pi * Real.exp (219 / 800 : ℝ) - (109 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (109 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (109 / 400 : ℝ)) := by
    have h := hpThetaJensenCell218_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (145329344761 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell218_endpointUpper :
    hpThetaJensenKernelEndpointUpper (109 / 800 : ℝ) (219 / 1600 : ℝ) ≤ (15077461537 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (219 / 800 : ℝ)) (41308367781192421 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (219 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell218_product_upper
  have hD : (289071931951 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (109 / 400 : ℝ) - (219 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell218_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell218_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (109 / 400 : ℝ) - (219 / 3200 : ℝ)) ≤
      (1 / (289071931951 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (289071931951 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((219 / 3200 : ℝ) - Real.pi * Real.exp (109 / 400 : ℝ)) ≤
      (2 / (289071931951 / 5000000000 : ℝ) : ℝ) := by
    rw [show (219 / 3200 : ℝ) - Real.pi * Real.exp (109 / 400 : ℝ) =
      -(Real.pi * Real.exp (109 / 400 : ℝ) - (219 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (41308367781192421 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (41308367781192421 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell218_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (109 / 800 : ℝ) (219 / 1600 : ℝ)) :
    (7453885309 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15077461537 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell218_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell218_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell219_leftExp :
    (3287215099 / 2500000000 : ℝ) ≤ Real.exp (219 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (219 / 800 : ℝ) (201718276681 / 200000000000 : ℝ)
    (3287215099 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell219_rightExp :
    Real.exp (11 / 40 : ℝ) ≤ (13165306749 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11 / 40 : ℝ) (252157695569 / 250000000000 : ℝ)
    (13165306749 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell219_denomUpper :
    Real.exp (40675660525511157 / 10000000000000000 : ℝ) ≤ (584146113311 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (40675660525511157 / 10000000000000000 : ℝ)
    (1135543554731 / 1000000000000 : ℝ) (584146113311 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell219_denomLower :
    (72619175639 / 1250000000 : ℝ) ≤ Real.exp (1269401707162201 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1269401707162201 / 312500000000000 : ℝ) (567674544313 /
    500000000000 : ℝ) (72619175639 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell219_product_lower :
    (1290886082162201 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (219 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell219_leftExp
    (by norm_num : (0 : ℝ) ≤ (3287215099 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell219_product_upper :
    Real.pi * Real.exp (11 / 40 : ℝ) ≤ (41360035525511157 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell219_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell219_endpointLower :
    (372083223 / 250000000 : ℝ) ≤ hpThetaTraceEndpointLower (219 / 1600 : ℝ) (11 / 80 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1290886082162201 / 312500000000000 : ℝ) (Real.pi * Real.exp (219 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell219_product_lower
  have hD : Real.exp (Real.pi * Real.exp (11 / 40 : ℝ) - (219 / 3200 : ℝ)) ≤
      (584146113311 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell219_denomUpper
    linarith [hpThetaJensenCell219_product_upper]
  have hi : (1 / (584146113311 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (11 / 40 : ℝ) - (219 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (584146113311 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (584146113311 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((219 / 3200 : ℝ) - Real.pi * Real.exp (11 / 40 : ℝ)) := by
    rw [show (219 / 3200 : ℝ) - Real.pi * Real.exp (11 / 40 : ℝ) =
      -(Real.pi * Real.exp (11 / 40 : ℝ) - (219 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (219 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (219 / 800 : ℝ)) := by
    have h := hpThetaJensenCell219_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (584146113311 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell219_endpointUpper :
    hpThetaJensenKernelEndpointUpper (219 / 1600 : ℝ) (11 / 80 : ℝ) ≤ (15052817737 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (11 / 40 : ℝ)) (41360035525511157 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (11 / 80 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell219_product_upper
  have hD : (72619175639 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (219 / 800 : ℝ) - (11 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell219_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell219_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (219 / 800 : ℝ) - (11 / 160 : ℝ)) ≤
      (1 / (72619175639 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (72619175639 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((11 / 160 : ℝ) - Real.pi * Real.exp (219 / 800 : ℝ)) ≤
      (2 / (72619175639 / 1250000000 : ℝ) : ℝ) := by
    rw [show (11 / 160 : ℝ) - Real.pi * Real.exp (219 / 800 : ℝ) =
      -(Real.pi * Real.exp (219 / 800 : ℝ) - (11 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (41360035525511157 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (41360035525511157 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell219_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (219 / 1600 : ℝ) (11 / 80 : ℝ)) :
    (372083223 / 250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15052817737 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell219_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell219_endpointUpper

def hpThetaJensenCellsBatch010Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3833523963 / 2500000000 : ℝ)
  | 1 => (3827777663 / 2500000000 : ℝ)
  | 2 => (7644020423 / 5000000000 : ℝ)
  | 3 => (24423819 / 16000000 : ℝ)
  | 4 => (3810412289 / 2500000000 : ℝ)
  | 5 => (1521832813 / 1000000000 : ℝ)
  | 6 => (15194924211 / 10000000000 : ℝ)
  | 7 => (3792859463 / 2500000000 : ℝ)
  | 8 => (3029573893 / 2000000000 : ℝ)
  | 9 => (30248439 / 20000000 : ℝ)
  | 10 => (7550244189 / 5000000000 : ℝ)
  | 11 => (15076676549 / 10000000000 : ℝ)
  | 12 => (3763196109 / 2500000000 : ℝ)
  | 13 => (3757203123 / 2500000000 : ℝ)
  | 14 => (3751190287 / 2500000000 : ℝ)
  | 15 => (2996126169 / 2000000000 : ℝ)
  | 16 => (14956422029 / 10000000000 : ℝ)
  | 17 => (7466067569 / 5000000000 : ℝ)
  | 18 => (7453885309 / 5000000000 : ℝ)
  | 19 => (372083223 / 250000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch010Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (15507259307 / 10000000000 : ℝ)
  | 1 => (15484089531 / 10000000000 : ℝ)
  | 2 => (15460834169 / 10000000000 : ℝ)
  | 3 => (15437493637 / 10000000000 : ℝ)
  | 4 => (15414068371 / 10000000000 : ℝ)
  | 5 => (38476397 / 25000000 : ℝ)
  | 6 => (3841741341 / 2500000000 : ℝ)
  | 7 => (3068657697 / 2000000000 : ℝ)
  | 8 => (3829882153 / 2500000000 : ℝ)
  | 9 => (15295686171 / 10000000000 : ℝ)
  | 10 => (15271761611 / 10000000000 : ℝ)
  | 11 => (95298471 / 62500000 : ℝ)
  | 12 => (15223667869 / 10000000000 : ℝ)
  | 13 => (949968723 / 625000000 : ℝ)
  | 14 => (15175250907 / 10000000000 : ℝ)
  | 15 => (15150922329 / 10000000000 : ℝ)
  | 16 => (605060571 / 400000000 : ℝ)
  | 17 => (3020405439 / 2000000000 : ℝ)
  | 18 => (15077461537 / 10000000000 : ℝ)
  | 19 => (15052817737 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch010_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((200 : ℝ) + (j.val : ℝ)) / 1600)
      (((200 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch010Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch010Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell200_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell201_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell202_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell203_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell204_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell205_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell206_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell207_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell208_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell209_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell210_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell211_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell212_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell213_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell214_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell215_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell216_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell217_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell218_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell219_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper] at h ⊢
    exact h

end HodgeProofHP
