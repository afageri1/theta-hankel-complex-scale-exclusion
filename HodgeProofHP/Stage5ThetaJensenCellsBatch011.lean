import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell220_leftExp :
    (3291326687 / 2500000000 : ℝ) ≤ Real.exp (11 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11 / 40 : ℝ) (40345231291 / 40000000000 : ℝ) (3291326687
    / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell220_rightExp :
    Real.exp (221 / 800 : ℝ) ≤ (13181773673 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (221 / 800 : ℝ) (504335091343 / 500000000000 : ℝ)
    (13181773673 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell220_denomUpper :
    Real.exp (40724267898681089 / 10000000000000000 : ℝ) ≤ (586992406051 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (40724267898681089 / 10000000000000000 : ℝ)
    (1135716054673 / 1000000000000 : ℝ) (586992406051 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell220_denomLower :
    (72972545911 / 1250000000 : ℝ) ≤ Real.exp (1270918667408213 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1270918667408213 / 312500000000000 : ℝ) (1135521329633 /
    1000000000000 : ℝ) (72972545911 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell220_product_lower :
    (1292500698658213 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (11 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell220_leftExp
    (by norm_num : (0 : ℝ) ≤ (3291326687 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell220_product_upper :
    Real.pi * Real.exp (221 / 800 : ℝ) ≤ (41411767898681089 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell220_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell220_endpointLower :
    (594352419 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (11 / 80 : ℝ) (221 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1292500698658213 / 312500000000000 : ℝ) (Real.pi * Real.exp (11 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell220_product_lower
  have hD : Real.exp (Real.pi * Real.exp (221 / 800 : ℝ) - (11 / 160 : ℝ)) ≤
      (586992406051 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell220_denomUpper
    linarith [hpThetaJensenCell220_product_upper]
  have hi : (1 / (586992406051 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (221 / 800 : ℝ) - (11 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (586992406051 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (586992406051 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((11 / 160 : ℝ) - Real.pi * Real.exp (221 / 800 : ℝ)) := by
    rw [show (11 / 160 : ℝ) - Real.pi * Real.exp (221 / 800 : ℝ) =
      -(Real.pi * Real.exp (221 / 800 : ℝ) - (11 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (11 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (11 / 40 : ℝ)) := by
    have h := hpThetaJensenCell220_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (586992406051 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell220_endpointUpper :
    hpThetaJensenKernelEndpointUpper (11 / 80 : ℝ) (221 / 1600 : ℝ) ≤ (15028096263 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (221 / 800 : ℝ)) (41411767898681089 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (221 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell220_product_upper
  have hD : (72972545911 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (11 / 40 : ℝ) - (221 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell220_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell220_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (11 / 40 : ℝ) - (221 / 3200 : ℝ)) ≤
      (1 / (72972545911 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (72972545911 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((221 / 3200 : ℝ) - Real.pi * Real.exp (11 / 40 : ℝ)) ≤
      (2 / (72972545911 / 1250000000 : ℝ) : ℝ) := by
    rw [show (221 / 3200 : ℝ) - Real.pi * Real.exp (11 / 40 : ℝ) =
      -(Real.pi * Real.exp (11 / 40 : ℝ) - (221 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (41411767898681089 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (41411767898681089 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell220_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (11 / 80 : ℝ) (221 / 1600 : ℝ)) :
    (594352419 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15028096263 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell220_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell220_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell221_leftExp :
    (13181773671 / 10000000000 : ℝ) ≤ Real.exp (221 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (221 / 800 : ℝ) (201734036537 / 200000000000 : ℝ)
    (13181773671 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell221_rightExp :
    Real.exp (111 / 400 : ℝ) ≤ (1649782649 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (111 / 400 : ℝ) (504354792317 / 500000000000 : ℝ)
    (1649782649 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell221_denomUpper :
    Real.exp (5096617496619857 / 1250000000000000 : ℝ) ≤ (117971276799 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (5096617496619857 / 1250000000000000 : ℝ) (1135888810487
    / 1000000000000 : ℝ) (117971276799 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell221_denomLower :
    (18332027399 / 312500000 : ℝ) ≤ Real.exp (5089750588828029 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5089750588828029 / 1250000000000000 : ℝ) (113569382613 /
    100000000000 : ℝ) (18332027399 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell221_product_lower :
    (5176469338828029 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (221 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell221_leftExp
    (by norm_num : (0 : ℝ) ≤ (13181773671 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell221_product_upper :
    Real.pi * Real.exp (111 / 400 : ℝ) ≤ (5182945621619857 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell221_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell221_endpointLower :
    (14834215747 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (221 / 1600 : ℝ) (111 / 800 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5176469338828029 / 1250000000000000 : ℝ) (Real.pi * Real.exp (221 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell221_product_lower
  have hD : Real.exp (Real.pi * Real.exp (111 / 400 : ℝ) - (221 / 3200 : ℝ)) ≤
      (117971276799 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell221_denomUpper
    linarith [hpThetaJensenCell221_product_upper]
  have hi : (1 / (117971276799 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (111 / 400 : ℝ) - (221 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (117971276799 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (117971276799 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((221 / 3200 : ℝ) - Real.pi * Real.exp (111 / 400 : ℝ)) := by
    rw [show (221 / 3200 : ℝ) - Real.pi * Real.exp (111 / 400 : ℝ) =
      -(Real.pi * Real.exp (111 / 400 : ℝ) - (221 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (221 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (221 / 800 : ℝ)) := by
    have h := hpThetaJensenCell221_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (117971276799 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell221_endpointUpper :
    hpThetaJensenKernelEndpointUpper (221 / 1600 : ℝ) (111 / 800 : ℝ) ≤ (15003297549 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (111 / 400 : ℝ)) (5182945621619857 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (111 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell221_product_upper
  have hD : (18332027399 / 312500000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (221 / 800 : ℝ) - (111 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell221_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell221_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (221 / 800 : ℝ) - (111 / 1600 : ℝ)) ≤
      (1 / (18332027399 / 312500000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (18332027399 / 312500000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((111 / 1600 : ℝ) - Real.pi * Real.exp (221 / 800 : ℝ)) ≤
      (2 / (18332027399 / 312500000 : ℝ) : ℝ) := by
    rw [show (111 / 1600 : ℝ) - Real.pi * Real.exp (221 / 800 : ℝ) =
      -(Real.pi * Real.exp (221 / 800 : ℝ) - (111 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (5182945621619857 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (5182945621619857 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell221_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (221 / 1600 : ℝ) (111 / 800 : ℝ)) :
    (14834215747 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15003297549 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell221_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell221_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell222_leftExp :
    (13198261191 / 10000000000 : ℝ) ≤ Real.exp (111 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (111 / 400 : ℝ) (1008709584633 / 1000000000000 : ℝ)
    (13198261191 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell222_rightExp :
    Real.exp (223 / 800 : ℝ) ≤ (6607384667 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (223 / 800 : ℝ) (504374494061 / 500000000000 : ℝ)
    (6607384667 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell222_denomUpper :
    Real.exp (20410838418154531 / 5000000000000000 : ℝ) ≤ (592738175761 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (20410838418154531 / 5000000000000000 : ℝ) (8875482989 /
    7812500000 : ℝ) (592738175761 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell222_denomLower :
    (147371765179 / 2500000000 : ℝ) ≤ Real.exp (5095834596444509 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5095834596444509 / 1250000000000000 : ℝ) (227173315703 /
    200000000000 : ℝ) (147371765179 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell222_product_lower :
    (5182943971444509 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (111 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell222_leftExp
    (by norm_num : (0 : ℝ) ≤ (13198261191 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell222_product_upper :
    Real.pi * Real.exp (223 / 800 : ℝ) ≤ (20757713418154531 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell222_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell222_endpointLower :
    (1851193147 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (111 / 800 : ℝ) (223 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5182943971444509 / 1250000000000000 : ℝ) (Real.pi * Real.exp (111 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell222_product_lower
  have hD : Real.exp (Real.pi * Real.exp (223 / 800 : ℝ) - (111 / 1600 : ℝ)) ≤
      (592738175761 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell222_denomUpper
    linarith [hpThetaJensenCell222_product_upper]
  have hi : (1 / (592738175761 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (223 / 800 : ℝ) - (111 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (592738175761 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (592738175761 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((111 / 1600 : ℝ) - Real.pi * Real.exp (223 / 800 : ℝ)) := by
    rw [show (111 / 1600 : ℝ) - Real.pi * Real.exp (223 / 800 : ℝ) =
      -(Real.pi * Real.exp (223 / 800 : ℝ) - (111 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (111 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (111 / 400 : ℝ)) := by
    have h := hpThetaJensenCell222_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (592738175761 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell222_endpointUpper :
    hpThetaJensenKernelEndpointUpper (111 / 800 : ℝ) (223 / 1600 : ℝ) ≤ (3744605513 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (223 / 800 : ℝ)) (20757713418154531 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (223 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell222_product_upper
  have hD : (147371765179 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (111 / 400 : ℝ) - (223 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell222_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell222_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (111 / 400 : ℝ) - (223 / 3200 : ℝ)) ≤
      (1 / (147371765179 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (147371765179 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((223 / 3200 : ℝ) - Real.pi * Real.exp (111 / 400 : ℝ)) ≤
      (2 / (147371765179 / 2500000000 : ℝ) : ℝ) := by
    rw [show (223 / 3200 : ℝ) - Real.pi * Real.exp (111 / 400 : ℝ) =
      -(Real.pi * Real.exp (111 / 400 : ℝ) - (223 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (20757713418154531 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (20757713418154531 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell222_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (111 / 800 : ℝ) (223 / 1600 : ℝ)) :
    (1851193147 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3744605513 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell222_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell222_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell223_leftExp :
    (13214769333 / 10000000000 : ℝ) ≤ Real.exp (223 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (223 / 800 : ℝ) (1008748988121 / 1000000000000 : ℝ)
    (13214769333 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell223_rightExp :
    Real.exp (7 / 25 : ℝ) ≤ (3307824531 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7 / 25 : ℝ) (1008788393149 / 1000000000000 : ℝ)
    (3307824531 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell223_denomUpper :
    Real.exp (10217619641817883 / 2500000000000000 : ℝ) ≤ (595637910507 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (10217619641817883 / 2500000000000000 : ℝ) (1136235091377
    / 1000000000000 : ℝ) (595637910507 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell223_denomLower :
    (296183523571 / 5000000000 : ℝ) ≤ Real.exp (5101926702299767 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5101926702299767 / 1250000000000000 : ℝ) (45441583487 /
    40000000000 : ℝ) (296183523571 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell223_product_lower :
    (5189426702299767 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (223 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell223_leftExp
    (by norm_num : (0 : ℝ) ≤ (13214769333 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell223_product_upper :
    Real.pi * Real.exp (7 / 25 : ℝ) ≤ (10391838391817883 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell223_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell223_endpointLower :
    (1478479921 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (223 / 1600 : ℝ) (7 / 50 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5189426702299767 / 1250000000000000 : ℝ) (Real.pi * Real.exp (223 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell223_product_lower
  have hD : Real.exp (Real.pi * Real.exp (7 / 25 : ℝ) - (223 / 3200 : ℝ)) ≤
      (595637910507 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell223_denomUpper
    linarith [hpThetaJensenCell223_product_upper]
  have hi : (1 / (595637910507 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (7 / 25 : ℝ) - (223 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (595637910507 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (595637910507 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((223 / 3200 : ℝ) - Real.pi * Real.exp (7 / 25 : ℝ)) := by
    rw [show (223 / 3200 : ℝ) - Real.pi * Real.exp (7 / 25 : ℝ) =
      -(Real.pi * Real.exp (7 / 25 : ℝ) - (223 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (223 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (223 / 800 : ℝ)) := by
    have h := hpThetaJensenCell223_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (595637910507 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell223_endpointUpper :
    hpThetaJensenKernelEndpointUpper (223 / 1600 : ℝ) (7 / 50 : ℝ) ≤ (7476735113 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (7 / 25 : ℝ)) (10391838391817883 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (7 / 50 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell223_product_upper
  have hD : (296183523571 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (223 / 800 : ℝ) - (7 / 100 : ℝ)) := by
    apply le_trans hpThetaJensenCell223_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell223_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (223 / 800 : ℝ) - (7 / 100 : ℝ)) ≤
      (1 / (296183523571 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (296183523571 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((7 / 100 : ℝ) - Real.pi * Real.exp (223 / 800 : ℝ)) ≤
      (2 / (296183523571 / 5000000000 : ℝ) : ℝ) := by
    rw [show (7 / 100 : ℝ) - Real.pi * Real.exp (223 / 800 : ℝ) =
      -(Real.pi * Real.exp (223 / 800 : ℝ) - (7 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (10391838391817883 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (10391838391817883 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell223_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (223 / 1600 : ℝ) (7 / 50 : ℝ)) :
    (1478479921 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7476735113 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell223_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell223_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell224_leftExp :
    (13231298123 / 10000000000 : ℝ) ≤ Real.exp (7 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7 / 25 : ℝ) (252197098287 / 250000000000 : ℝ)
    (13231298123 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell224_rightExp :
    Real.exp (9 / 32 : ℝ) ≤ (3311961897 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9 / 32 : ℝ) (201765559943 / 200000000000 : ℝ)
    (3311961897 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell224_denomUpper :
    Real.exp (10229836311881921 / 2500000000000000 : ℝ) ≤ (119711143721 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (10229836311881921 / 2500000000000000 : ℝ) (1136408617241
    / 1000000000000 : ℝ) (119711143721 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell224_denomLower :
    (119052993061 / 2000000000 : ℝ) ≤ Real.exp (5108026916603977 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5108026916603977 / 1250000000000000 : ℝ) (113621285251 /
    100000000000 : ℝ) (119052993061 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell224_product_lower :
    (5195917541603977 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (7 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell224_leftExp
    (by norm_num : (0 : ℝ) ≤ (13231298123 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell224_product_upper :
    Real.pi * Real.exp (9 / 32 : ℝ) ≤ (10404836311881921 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell224_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell224_endpointLower :
    (14759978301 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (7 / 50 : ℝ) (9 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5195917541603977 / 1250000000000000 : ℝ) (Real.pi * Real.exp (7 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell224_product_lower
  have hD : Real.exp (Real.pi * Real.exp (9 / 32 : ℝ) - (7 / 100 : ℝ)) ≤
      (119711143721 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell224_denomUpper
    linarith [hpThetaJensenCell224_product_upper]
  have hi : (1 / (119711143721 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (9 / 32 : ℝ) - (7 / 100 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (119711143721 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (119711143721 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((7 / 100 : ℝ) - Real.pi * Real.exp (9 / 32 : ℝ)) := by
    rw [show (7 / 100 : ℝ) - Real.pi * Real.exp (9 / 32 : ℝ) =
      -(Real.pi * Real.exp (9 / 32 : ℝ) - (7 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (7 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (7 / 25 : ℝ)) := by
    have h := hpThetaJensenCell224_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (119711143721 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell224_endpointUpper :
    hpThetaJensenKernelEndpointUpper (7 / 50 : ℝ) (9 / 64 : ℝ) ≤ (14928442523 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (9 / 32 : ℝ)) (10404836311881921 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (9 / 64 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell224_product_upper
  have hD : (119052993061 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (7 / 25 : ℝ) - (9 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell224_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell224_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (7 / 25 : ℝ) - (9 / 128 : ℝ)) ≤
      (1 / (119052993061 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (119052993061 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((9 / 128 : ℝ) - Real.pi * Real.exp (7 / 25 : ℝ)) ≤
      (2 / (119052993061 / 2000000000 : ℝ) : ℝ) := by
    rw [show (9 / 128 : ℝ) - Real.pi * Real.exp (7 / 25 : ℝ) =
      -(Real.pi * Real.exp (7 / 25 : ℝ) - (9 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (10404836311881921 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (10404836311881921 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell224_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (7 / 50 : ℝ) (9 / 64 : ℝ)) :
    (14759978301 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (14928442523 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell224_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell224_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell225_leftExp :
    (13247847587 / 10000000000 : ℝ) ≤ Real.exp (9 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9 / 32 : ℝ) (504413899857 / 500000000000 : ℝ)
    (13247847587 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell225_rightExp :
    Real.exp (113 / 400 : ℝ) ≤ (1658052219 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (113 / 400 : ℝ) (1008867207821 / 1000000000000 : ℝ)
    (1658052219 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell225_denomUpper :
    Real.exp (5121034619844867 / 1250000000000000 : ℝ) ≤ (300745865759 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (5121034619844867 / 1250000000000000 : ℝ) (227316480117 /
    200000000000 : ℝ) (300745865759 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell225_denomLower :
    (74772618187 / 1250000000 : ℝ) ≤ Real.exp (5114135249567313 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5114135249567313 / 1250000000000000 : ℝ) (1136386374919
    / 1000000000000 : ℝ) (74772618187 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell225_product_lower :
    (5202416499567313 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (9 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell225_leftExp
    (by norm_num : (0 : ℝ) ≤ (13247847587 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell225_product_upper :
    Real.pi * Real.exp (113 / 400 : ℝ) ≤ (5208925244844867 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell225_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell225_endpointLower :
    (14735082899 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (9 / 64 : ℝ) (113 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5202416499567313 / 1250000000000000 : ℝ) (Real.pi * Real.exp (9 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell225_product_lower
  have hD : Real.exp (Real.pi * Real.exp (113 / 400 : ℝ) - (9 / 128 : ℝ)) ≤
      (300745865759 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell225_denomUpper
    linarith [hpThetaJensenCell225_product_upper]
  have hi : (1 / (300745865759 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (113 / 400 : ℝ) - (9 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (300745865759 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (300745865759 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((9 / 128 : ℝ) - Real.pi * Real.exp (113 / 400 : ℝ)) := by
    rw [show (9 / 128 : ℝ) - Real.pi * Real.exp (113 / 400 : ℝ) =
      -(Real.pi * Real.exp (113 / 400 : ℝ) - (9 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (9 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (9 / 32 : ℝ)) := by
    have h := hpThetaJensenCell225_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (300745865759 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell225_endpointUpper :
    hpThetaJensenKernelEndpointUpper (9 / 64 : ℝ) (113 / 800 : ℝ) ≤ (14903339397 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (113 / 400 : ℝ)) (5208925244844867 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (113 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell225_product_upper
  have hD : (74772618187 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (9 / 32 : ℝ) - (113 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell225_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell225_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (9 / 32 : ℝ) - (113 / 1600 : ℝ)) ≤
      (1 / (74772618187 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (74772618187 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((113 / 1600 : ℝ) - Real.pi * Real.exp (9 / 32 : ℝ)) ≤
      (2 / (74772618187 / 1250000000 : ℝ) : ℝ) := by
    rw [show (113 / 1600 : ℝ) - Real.pi * Real.exp (9 / 32 : ℝ) =
      -(Real.pi * Real.exp (9 / 32 : ℝ) - (113 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (5208925244844867 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (5208925244844867 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell225_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (9 / 64 : ℝ) (113 / 800 : ℝ)) :
    (14735082899 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (14903339397 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell225_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell225_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell226_leftExp :
    (53057671 / 40000000 : ℝ) ≤ Real.exp (113 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (113 / 400 : ℝ) (50443360391 / 50000000000 : ℝ) (53057671
    / 40000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell226_rightExp :
    Real.exp (227 / 800 : ℝ) ≤ (13281008641 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (227 / 800 : ℝ) (504453308733 / 500000000000 : ℝ)
    (13281008641 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell226_denomUpper :
    Real.exp (41017273779505113 / 10000000000000000 : ℝ) ≤ (120889216311 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (41017273779505113 / 10000000000000000 : ℝ)
    (1136756441797 / 1000000000000 : ℝ) (120889216311 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell226_denomLower :
    (150278779727 / 2500000000 : ℝ) ≤ Real.exp (20481006844029 / 5000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (20481006844029 / 5000000000000 : ℝ) (142070019349 /
    125000000000 : ℝ) (150278779727 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell226_product_lower :
    (20835694344029 / 5000000000000 : ℝ) ≤ Real.pi * Real.exp (113 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell226_leftExp
    (by norm_num : (0 : ℝ) ≤ (53057671 / 40000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell226_product_upper :
    Real.pi * Real.exp (227 / 800 : ℝ) ≤ (41723523779505113 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell226_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell226_endpointLower :
    (7355056729 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (113 / 800 : ℝ) (227 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (20835694344029 / 5000000000000 : ℝ) (Real.pi * Real.exp (113 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell226_product_lower
  have hD : Real.exp (Real.pi * Real.exp (227 / 800 : ℝ) - (113 / 1600 : ℝ)) ≤
      (120889216311 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell226_denomUpper
    linarith [hpThetaJensenCell226_product_upper]
  have hi : (1 / (120889216311 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (227 / 800 : ℝ) - (113 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (120889216311 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (120889216311 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((113 / 1600 : ℝ) - Real.pi * Real.exp (227 / 800 : ℝ)) := by
    rw [show (113 / 1600 : ℝ) - Real.pi * Real.exp (227 / 800 : ℝ) =
      -(Real.pi * Real.exp (227 / 800 : ℝ) - (113 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (113 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (113 / 400 : ℝ)) := by
    have h := hpThetaJensenCell226_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (120889216311 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell226_endpointUpper :
    hpThetaJensenKernelEndpointUpper (113 / 800 : ℝ) (227 / 1600 : ℝ) ≤ (1859770163 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (227 / 800 : ℝ)) (41723523779505113 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (227 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell226_product_upper
  have hD : (150278779727 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (113 / 400 : ℝ) - (227 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell226_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell226_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (113 / 400 : ℝ) - (227 / 3200 : ℝ)) ≤
      (1 / (150278779727 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (150278779727 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((227 / 3200 : ℝ) - Real.pi * Real.exp (113 / 400 : ℝ)) ≤
      (2 / (150278779727 / 2500000000 : ℝ) : ℝ) := by
    rw [show (227 / 3200 : ℝ) - Real.pi * Real.exp (113 / 400 : ℝ) =
      -(Real.pi * Real.exp (113 / 400 : ℝ) - (227 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (41723523779505113 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (41723523779505113 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell226_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (113 / 800 : ℝ) (227 / 1600 : ℝ)) :
    (7355056729 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1859770163 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell226_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell226_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell227_leftExp :
    (2593947 / 1953125 : ℝ) ≤ Real.exp (227 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (227 / 800 : ℝ) (201781323493 / 200000000000 : ℝ)
    (2593947 / 1953125 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell227_rightExp :
    Real.exp (57 / 200 : ℝ) ≤ (6648810141 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (57 / 200 : ℝ) (20178920573 / 20000000000 : ℝ)
    (6648810141 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell227_denomUpper :
    Real.exp (20533167897294613 / 5000000000000000 : ℝ) ≤ (607418902487 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (20533167897294613 / 5000000000000000 : ℝ) (142116342661
    / 125000000000 : ℝ) (607418902487 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell227_denomLower :
    (151016904577 / 2500000000 : ℝ) ≤ Real.exp (4004981493687 / 976562500000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4004981493687 / 976562500000 : ℝ) (1136734192549 /
    1000000000000 : ℝ) (151016904577 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell227_product_lower :
    (1018640392953 / 244140625000 : ℝ) ≤ Real.pi * Real.exp (227 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell227_leftExp
    (by norm_num : (0 : ℝ) ≤ (2593947 / 1953125 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell227_product_upper :
    Real.pi * Real.exp (57 / 200 : ℝ) ≤ (20887855397294613 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell227_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell227_endpointLower :
    (458908451 / 312500000 : ℝ) ≤ hpThetaTraceEndpointLower (227 / 1600 : ℝ) (57 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1018640392953 / 244140625000 : ℝ) (Real.pi * Real.exp (227 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell227_product_lower
  have hD : Real.exp (Real.pi * Real.exp (57 / 200 : ℝ) - (227 / 3200 : ℝ)) ≤
      (607418902487 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell227_denomUpper
    linarith [hpThetaJensenCell227_product_upper]
  have hi : (1 / (607418902487 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (57 / 200 : ℝ) - (227 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (607418902487 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (607418902487 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((227 / 3200 : ℝ) - Real.pi * Real.exp (57 / 200 : ℝ)) := by
    rw [show (227 / 3200 : ℝ) - Real.pi * Real.exp (57 / 200 : ℝ) =
      -(Real.pi * Real.exp (57 / 200 : ℝ) - (227 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (227 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (227 / 800 : ℝ)) := by
    have h := hpThetaJensenCell227_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (607418902487 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell227_endpointUpper :
    hpThetaJensenKernelEndpointUpper (227 / 1600 : ℝ) (57 / 400 : ℝ) ≤ (7426454347 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (57 / 200 : ℝ)) (20887855397294613 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (57 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell227_product_upper
  have hD : (151016904577 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (227 / 800 : ℝ) - (57 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell227_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell227_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (227 / 800 : ℝ) - (57 / 800 : ℝ)) ≤
      (1 / (151016904577 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (151016904577 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((57 / 800 : ℝ) - Real.pi * Real.exp (227 / 800 : ℝ)) ≤
      (2 / (151016904577 / 2500000000 : ℝ) : ℝ) := by
    rw [show (57 / 800 : ℝ) - Real.pi * Real.exp (227 / 800 : ℝ) =
      -(Real.pi * Real.exp (227 / 800 : ℝ) - (57 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (20887855397294613 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (20887855397294613 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell227_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (227 / 1600 : ℝ) (57 / 400 : ℝ)) :
    (458908451 / 312500000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7426454347 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell227_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell227_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell228_leftExp :
    (332440507 / 250000000 : ℝ) ≤ Real.exp (57 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (57 / 200 : ℝ) (1008946028649 / 1000000000000 : ℝ)
    (332440507 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell228_rightExp :
    Real.exp (229 / 800 : ℝ) ≤ (133142527 / 100000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (229 / 800 : ℝ) (504492720687 / 500000000000 : ℝ)
    (133142527 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell228_denomUpper :
    Real.exp (411154630825511 / 100000000000000 : ℝ) ≤ (12208206577 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (411154630825511 / 100000000000000 : ℝ) (22742105989 /
    20000000000 : ℝ) (12208206577 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell228_denomLower :
    (607038576673 / 10000000000 : ℝ) ≤ Real.exp (128312726533393 / 31250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (128312726533393 / 31250000000000 : ℝ) (1136908488559 /
    1000000000000 : ℝ) (607038576673 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell228_product_lower :
    (130549054658393 / 31250000000000 : ℝ) ≤ Real.pi * Real.exp (57 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell228_leftExp
    (by norm_num : (0 : ℝ) ≤ (332440507 / 250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell228_product_upper :
    Real.pi * Real.exp (229 / 800 : ℝ) ≤ (418279630825511 / 100000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell228_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell228_endpointLower :
    (14659954271 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (57 / 400 : ℝ) (229 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (130549054658393 / 31250000000000 : ℝ) (Real.pi * Real.exp (57 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell228_product_lower
  have hD : Real.exp (Real.pi * Real.exp (229 / 800 : ℝ) - (57 / 800 : ℝ)) ≤
      (12208206577 / 200000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell228_denomUpper
    linarith [hpThetaJensenCell228_product_upper]
  have hi : (1 / (12208206577 / 200000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (229 / 800 : ℝ) - (57 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (12208206577 / 200000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (12208206577 / 200000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((57 / 800 : ℝ) - Real.pi * Real.exp (229 / 800 : ℝ)) := by
    rw [show (57 / 800 : ℝ) - Real.pi * Real.exp (229 / 800 : ℝ) =
      -(Real.pi * Real.exp (229 / 800 : ℝ) - (57 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (57 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (57 / 200 : ℝ)) := by
    have h := hpThetaJensenCell228_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (12208206577 / 200000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell228_endpointUpper :
    hpThetaJensenKernelEndpointUpper (57 / 400 : ℝ) (229 / 1600 : ℝ) ≤ (3706895509 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (229 / 800 : ℝ)) (418279630825511 / 100000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (229 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell228_product_upper
  have hD : (607038576673 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (57 / 200 : ℝ) - (229 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell228_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell228_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (57 / 200 : ℝ) - (229 / 3200 : ℝ)) ≤
      (1 / (607038576673 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (607038576673 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((229 / 3200 : ℝ) - Real.pi * Real.exp (57 / 200 : ℝ)) ≤
      (2 / (607038576673 / 10000000000 : ℝ) : ℝ) := by
    rw [show (229 / 3200 : ℝ) - Real.pi * Real.exp (57 / 200 : ℝ) =
      -(Real.pi * Real.exp (57 / 200 : ℝ) - (229 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (418279630825511 / 100000000000000 : ℝ) ^ 2 - 6 *
      (418279630825511 / 100000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell228_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (57 / 400 : ℝ) (229 / 1600 : ℝ)) :
    (14659954271 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3706895509 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell228_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell228_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell229_leftExp :
    (13314252699 / 10000000000 : ℝ) ≤ Real.exp (229 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (229 / 800 : ℝ) (1008985441373 / 1000000000000 : ℝ)
    (13314252699 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell229_rightExp :
    Real.exp (23 / 80 : ℝ) ≤ (6665452961 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (23 / 80 : ℝ) (504512427819 / 500000000000 : ℝ)
    (6665452961 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell229_denomUpper :
    Real.exp (20582327864106873 / 5000000000000000 : ℝ) ≤ (76677562073 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (20582327864106873 / 5000000000000000 : ℝ) (1137280116693
    / 1000000000000 : ℝ) (76677562073 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell229_denomLower :
    (61002812917 / 1000000000 : ℝ) ≤ Real.exp (5138649970644601 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5138649970644601 / 1250000000000000 : ℝ) (142135380407 /
    125000000000 : ℝ) (61002812917 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell229_product_lower :
    (5228493720644601 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (229 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell229_leftExp
    (by norm_num : (0 : ℝ) ≤ (13314252699 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell229_product_upper :
    Real.pi * Real.exp (23 / 80 : ℝ) ≤ (20940140364106873 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell229_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell229_endpointLower :
    (2926953087 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (229 / 1600 : ℝ) (23 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5228493720644601 / 1250000000000000 : ℝ) (Real.pi * Real.exp (229 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell229_product_lower
  have hD : Real.exp (Real.pi * Real.exp (23 / 80 : ℝ) - (229 / 3200 : ℝ)) ≤
      (76677562073 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell229_denomUpper
    linarith [hpThetaJensenCell229_product_upper]
  have hi : (1 / (76677562073 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (23 / 80 : ℝ) - (229 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (76677562073 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (76677562073 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((229 / 3200 : ℝ) - Real.pi * Real.exp (23 / 80 : ℝ)) := by
    rw [show (229 / 3200 : ℝ) - Real.pi * Real.exp (23 / 80 : ℝ) =
      -(Real.pi * Real.exp (23 / 80 : ℝ) - (229 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (229 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (229 / 800 : ℝ)) := by
    have h := hpThetaJensenCell229_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (76677562073 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell229_endpointUpper :
    hpThetaJensenKernelEndpointUpper (229 / 1600 : ℝ) (23 / 160 : ℝ) ≤ (592087271 / 400000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (23 / 80 : ℝ)) (20940140364106873 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (23 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell229_product_upper
  have hD : (61002812917 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (229 / 800 : ℝ) - (23 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell229_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell229_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (229 / 800 : ℝ) - (23 / 320 : ℝ)) ≤
      (1 / (61002812917 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (61002812917 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((23 / 320 : ℝ) - Real.pi * Real.exp (229 / 800 : ℝ)) ≤
      (2 / (61002812917 / 1000000000 : ℝ) : ℝ) := by
    rw [show (23 / 320 : ℝ) - Real.pi * Real.exp (229 / 800 : ℝ) =
      -(Real.pi * Real.exp (229 / 800 : ℝ) - (23 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (20940140364106873 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (20940140364106873 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell229_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (229 / 1600 : ℝ) (23 / 160 : ℝ)) :
    (2926953087 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (592087271 / 400000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell229_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell229_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell230_leftExp :
    (13330905921 / 10000000000 : ℝ) ≤ Real.exp (23 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (23 / 80 : ℝ) (1009024855637 / 1000000000000 : ℝ)
    (13330905921 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell230_rightExp :
    Real.exp (231 / 800 : ℝ) ≤ (6673789987 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (231 / 800 : ℝ) (1009064271441 / 1000000000000 : ℝ)
    (6673789987 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell230_denomUpper :
    Real.exp (20606956906629291 / 5000000000000000 : ℝ) ≤ (154112385653 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (20606956906629291 / 5000000000000000 : ℝ) (56872759671 /
    50000000000 : ℝ) (154112385653 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell230_denomLower :
    (306518205553 / 5000000000 : ℝ) ≤ Real.exp (5144799049270779 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5144799049270779 / 1250000000000000 : ℝ) (568628928509 /
    500000000000 : ℝ) (306518205553 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell230_product_lower :
    (5235033424270779 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (23 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell230_leftExp
    (by norm_num : (0 : ℝ) ≤ (13330905921 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell230_product_upper :
    Real.pi * Real.exp (231 / 800 : ℝ) ≤ (20966331906629291 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell230_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell230_endpointLower :
    (14609504373 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (23 / 160 : ℝ) (231 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5235033424270779 / 1250000000000000 : ℝ) (Real.pi * Real.exp (23 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell230_product_lower
  have hD : Real.exp (Real.pi * Real.exp (231 / 800 : ℝ) - (23 / 320 : ℝ)) ≤
      (154112385653 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell230_denomUpper
    linarith [hpThetaJensenCell230_product_upper]
  have hi : (1 / (154112385653 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (231 / 800 : ℝ) - (23 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (154112385653 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (154112385653 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((23 / 320 : ℝ) - Real.pi * Real.exp (231 / 800 : ℝ)) := by
    rw [show (23 / 320 : ℝ) - Real.pi * Real.exp (231 / 800 : ℝ) =
      -(Real.pi * Real.exp (231 / 800 : ℝ) - (23 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (23 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (23 / 80 : ℝ)) := by
    have h := hpThetaJensenCell230_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (154112385653 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell230_endpointUpper :
    hpThetaJensenKernelEndpointUpper (23 / 160 : ℝ) (231 / 1600 : ℝ) ≤ (14776708381 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (231 / 800 : ℝ)) (20966331906629291 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (231 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell230_product_upper
  have hD : (306518205553 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (23 / 80 : ℝ) - (231 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell230_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell230_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (23 / 80 : ℝ) - (231 / 3200 : ℝ)) ≤
      (1 / (306518205553 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (306518205553 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((231 / 3200 : ℝ) - Real.pi * Real.exp (23 / 80 : ℝ)) ≤
      (2 / (306518205553 / 5000000000 : ℝ) : ℝ) := by
    rw [show (231 / 3200 : ℝ) - Real.pi * Real.exp (23 / 80 : ℝ) =
      -(Real.pi * Real.exp (23 / 80 : ℝ) - (231 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (20966331906629291 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (20966331906629291 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell230_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (23 / 160 : ℝ) (231 / 1600 : ℝ)) :
    (14609504373 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (14776708381 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell230_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell230_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell231_leftExp :
    (3336894993 / 2500000000 : ℝ) ≤ Real.exp (231 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (231 / 800 : ℝ) (12613303393 / 12500000000 : ℝ)
    (3336894993 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell231_rightExp :
    Real.exp (29 / 100 : ℝ) ≤ (13364274881 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (29 / 100 : ℝ) (63068980549 / 62500000000 : ℝ)
    (13364274881 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell231_denomUpper :
    Real.exp (41263237416225433 / 10000000000000000 : ℝ) ≤ (2477990419 / 40000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (41263237416225433 / 10000000000000000 : ℝ)
    (1137630530021 / 1000000000000 : ℝ) (2477990419 / 40000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell231_denomLower :
    (308031779659 / 5000000000 : ℝ) ≤ Real.exp (1287739076856107 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1287739076856107 / 312500000000000 : ℝ) (142179116281 /
    125000000000 : ℝ) (308031779659 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell231_product_lower :
    (1310395326856107 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (231 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell231_leftExp
    (by norm_num : (0 : ℝ) ≤ (3336894993 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell231_product_upper :
    Real.pi * Real.exp (29 / 100 : ℝ) ≤ (41985112416225433 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell231_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell231_endpointLower :
    (3646042887 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (231 / 1600 : ℝ) (29 / 200 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1310395326856107 / 312500000000000 : ℝ) (Real.pi * Real.exp (231 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell231_product_lower
  have hD : Real.exp (Real.pi * Real.exp (29 / 100 : ℝ) - (231 / 3200 : ℝ)) ≤
      (2477990419 / 40000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell231_denomUpper
    linarith [hpThetaJensenCell231_product_upper]
  have hi : (1 / (2477990419 / 40000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (29 / 100 : ℝ) - (231 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2477990419 / 40000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2477990419 / 40000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((231 / 3200 : ℝ) - Real.pi * Real.exp (29 / 100 : ℝ)) := by
    rw [show (231 / 3200 : ℝ) - Real.pi * Real.exp (29 / 100 : ℝ) =
      -(Real.pi * Real.exp (29 / 100 : ℝ) - (231 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (231 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (231 / 800 : ℝ)) := by
    have h := hpThetaJensenCell231_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2477990419 / 40000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell231_endpointUpper :
    hpThetaJensenKernelEndpointUpper (231 / 1600 : ℝ) (29 / 200 : ℝ) ≤ (1475116231 / 1000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (29 / 100 : ℝ)) (41985112416225433 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (29 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell231_product_upper
  have hD : (308031779659 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (231 / 800 : ℝ) - (29 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell231_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell231_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (231 / 800 : ℝ) - (29 / 400 : ℝ)) ≤
      (1 / (308031779659 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (308031779659 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((29 / 400 : ℝ) - Real.pi * Real.exp (231 / 800 : ℝ)) ≤
      (2 / (308031779659 / 5000000000 : ℝ) : ℝ) := by
    rw [show (29 / 400 : ℝ) - Real.pi * Real.exp (231 / 800 : ℝ) =
      -(Real.pi * Real.exp (231 / 800 : ℝ) - (29 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (41985112416225433 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (41985112416225433 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell231_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (231 / 1600 : ℝ) (29 / 200 : ℝ)) :
    (3646042887 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1475116231 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell231_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell231_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell232_leftExp :
    (41763359 / 31250000 : ℝ) ≤ Real.exp (29 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (29 / 100 : ℝ) (1009103688783 / 1000000000000 : ℝ)
    (41763359 / 31250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell232_rightExp :
    Real.exp (233 / 800 : ℝ) ≤ (1338099067 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (233 / 800 : ℝ) (1009143107667 / 1000000000000 : ℝ)
    (1338099067 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell232_denomUpper :
    Real.exp (4131262662193731 / 1000000000000000 : ℝ) ≤ (38910301397 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4131262662193731 / 1000000000000000 : ℝ) (113780612691 /
    100000000000 : ℝ) (38910301397 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell232_denomLower :
    (123821942421 / 2000000000 : ℝ) ≤ Real.exp (2014500685977 / 488281250000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2014500685977 / 488281250000 : ℝ) (1137608263369 /
    1000000000000 : ℝ) (123821942421 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell232_product_lower :
    (16400429315941 / 3906250000000 : ℝ) ≤ Real.pi * Real.exp (29 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell232_leftExp
    (by norm_num : (0 : ℝ) ≤ (41763359 / 31250000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell232_product_upper :
    Real.pi * Real.exp (233 / 800 : ℝ) ≤ (4203762662193731 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell232_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell232_endpointLower :
    (14558767417 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (29 / 200 : ℝ) (233 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (16400429315941 / 3906250000000 : ℝ) (Real.pi * Real.exp (29 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell232_product_lower
  have hD : Real.exp (Real.pi * Real.exp (233 / 800 : ℝ) - (29 / 400 : ℝ)) ≤
      (38910301397 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell232_denomUpper
    linarith [hpThetaJensenCell232_product_upper]
  have hi : (1 / (38910301397 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (233 / 800 : ℝ) - (29 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (38910301397 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (38910301397 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((29 / 400 : ℝ) - Real.pi * Real.exp (233 / 800 : ℝ)) := by
    rw [show (29 / 400 : ℝ) - Real.pi * Real.exp (233 / 800 : ℝ) =
      -(Real.pi * Real.exp (233 / 800 : ℝ) - (29 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (29 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (29 / 100 : ℝ)) := by
    have h := hpThetaJensenCell232_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (38910301397 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell232_endpointUpper :
    hpThetaJensenKernelEndpointUpper (29 / 200 : ℝ) (233 / 1600 : ℝ) ≤ (920346501 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (233 / 800 : ℝ)) (4203762662193731 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (233 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell232_product_upper
  have hD : (123821942421 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (29 / 100 : ℝ) - (233 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell232_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell232_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (29 / 100 : ℝ) - (233 / 3200 : ℝ)) ≤
      (1 / (123821942421 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (123821942421 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((233 / 3200 : ℝ) - Real.pi * Real.exp (29 / 100 : ℝ)) ≤
      (2 / (123821942421 / 2000000000 : ℝ) : ℝ) := by
    rw [show (233 / 3200 : ℝ) - Real.pi * Real.exp (29 / 100 : ℝ) =
      -(Real.pi * Real.exp (29 / 100 : ℝ) - (233 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4203762662193731 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (4203762662193731 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell232_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (29 / 200 : ℝ) (233 / 1600 : ℝ)) :
    (14558767417 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (920346501 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell232_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell232_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell233_leftExp :
    (3345247667 / 2500000000 : ℝ) ≤ Real.exp (233 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (233 / 800 : ℝ) (504571553833 / 500000000000 : ℝ)
    (3345247667 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell233_rightExp :
    Real.exp (117 / 400 : ℝ) ≤ (6698863683 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (117 / 400 : ℝ) (1009182528089 / 1000000000000 : ℝ)
    (6698863683 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell233_denomUpper :
    Real.exp (20681040754467019 / 5000000000000000 : ℝ) ≤ (62565133551 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (20681040754467019 / 5000000000000000 : ℝ) (568990992239
    / 500000000000 : ℝ) (62565133551 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell233_denomLower :
    (311087503977 / 5000000000 : ℝ) ≤ Real.exp (1290823851083233 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1290823851083233 / 312500000000000 : ℝ) (4551135427 /
    4000000000 : ℝ) (311087503977 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell233_product_lower :
    (1313675413583233 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (233 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell233_leftExp
    (by norm_num : (0 : ℝ) ≤ (3345247667 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell233_product_upper :
    Real.pi * Real.exp (117 / 400 : ℝ) ≤ (21045103254467019 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell233_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell233_endpointLower :
    (7266646219 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (233 / 1600 : ℝ) (117 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1313675413583233 / 312500000000000 : ℝ) (Real.pi * Real.exp (233 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell233_product_lower
  have hD : Real.exp (Real.pi * Real.exp (117 / 400 : ℝ) - (233 / 3200 : ℝ)) ≤
      (62565133551 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell233_denomUpper
    linarith [hpThetaJensenCell233_product_upper]
  have hi : (1 / (62565133551 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (117 / 400 : ℝ) - (233 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (62565133551 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (62565133551 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((233 / 3200 : ℝ) - Real.pi * Real.exp (117 / 400 : ℝ)) := by
    rw [show (233 / 3200 : ℝ) - Real.pi * Real.exp (117 / 400 : ℝ) =
      -(Real.pi * Real.exp (117 / 400 : ℝ) - (233 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (233 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (233 / 800 : ℝ)) := by
    have h := hpThetaJensenCell233_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (62565133551 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell233_endpointUpper :
    hpThetaJensenKernelEndpointUpper (233 / 1600 : ℝ) (117 / 800 : ℝ) ≤ (7349926987 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (117 / 400 : ℝ)) (21045103254467019 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (117 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell233_product_upper
  have hD : (311087503977 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (233 / 800 : ℝ) - (117 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell233_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell233_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (233 / 800 : ℝ) - (117 / 1600 : ℝ)) ≤
      (1 / (311087503977 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (311087503977 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((117 / 1600 : ℝ) - Real.pi * Real.exp (233 / 800 : ℝ)) ≤
      (2 / (311087503977 / 5000000000 : ℝ) : ℝ) := by
    rw [show (117 / 1600 : ℝ) - Real.pi * Real.exp (233 / 800 : ℝ) =
      -(Real.pi * Real.exp (233 / 800 : ℝ) - (117 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (21045103254467019 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (21045103254467019 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell233_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (233 / 1600 : ℝ) (117 / 800 : ℝ)) :
    (7266646219 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7349926987 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell233_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell233_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell234_leftExp :
    (2679545473 / 2000000000 : ℝ) ≤ Real.exp (117 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (117 / 400 : ℝ) (126147816011 / 125000000000 : ℝ)
    (2679545473 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell234_rightExp :
    Real.exp (47 / 160 : ℝ) ≤ (13414484997 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (47 / 160 : ℝ) (252305487513 / 250000000000 : ℝ)
    (13414484997 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell234_denomUpper :
    Real.exp (41411602165180221 / 10000000000000000 : ℝ) ≤ (78594660759 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (41411602165180221 / 10000000000000000 : ℝ)
    (1138158103151 / 1000000000000 : ℝ) (78594660759 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell234_denomLower :
    (625259587671 / 10000000000 : ℝ) ≤ Real.exp (1033895452701627 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1033895452701627 / 250000000000000 : ℝ) (284489927707 /
    250000000000 : ℝ) (625259587671 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell234_product_lower :
    (1052254827701627 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (117 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell234_leftExp
    (by norm_num : (0 : ℝ) ≤ (2679545473 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell234_product_upper :
    Real.pi * Real.exp (47 / 160 : ℝ) ≤ (42142852165180221 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell234_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell234_endpointLower :
    (3626936767 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (117 / 800 : ℝ) (47 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1052254827701627 / 250000000000000 : ℝ) (Real.pi * Real.exp (117 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell234_product_lower
  have hD : Real.exp (Real.pi * Real.exp (47 / 160 : ℝ) - (117 / 1600 : ℝ)) ≤
      (78594660759 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell234_denomUpper
    linarith [hpThetaJensenCell234_product_upper]
  have hi : (1 / (78594660759 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (47 / 160 : ℝ) - (117 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (78594660759 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (78594660759 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((117 / 1600 : ℝ) - Real.pi * Real.exp (47 / 160 : ℝ)) := by
    rw [show (117 / 1600 : ℝ) - Real.pi * Real.exp (47 / 160 : ℝ) =
      -(Real.pi * Real.exp (47 / 160 : ℝ) - (117 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (117 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (117 / 400 : ℝ)) := by
    have h := hpThetaJensenCell234_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (78594660759 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell234_endpointUpper :
    hpThetaJensenKernelEndpointUpper (117 / 800 : ℝ) (47 / 320 : ℝ) ≤ (14674092637 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (47 / 160 : ℝ)) (42142852165180221 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (47 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell234_product_upper
  have hD : (625259587671 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (117 / 400 : ℝ) - (47 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell234_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell234_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (117 / 400 : ℝ) - (47 / 640 : ℝ)) ≤
      (1 / (625259587671 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (625259587671 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((47 / 640 : ℝ) - Real.pi * Real.exp (117 / 400 : ℝ)) ≤
      (2 / (625259587671 / 10000000000 : ℝ) : ℝ) := by
    rw [show (47 / 640 : ℝ) - Real.pi * Real.exp (117 / 400 : ℝ) =
      -(Real.pi * Real.exp (117 / 400 : ℝ) - (47 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (42142852165180221 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (42142852165180221 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell234_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (117 / 800 : ℝ) (47 / 320 : ℝ)) :
    (3626936767 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (14674092637 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell234_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell234_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell235_leftExp :
    (3353621249 / 2500000000 : ℝ) ≤ Real.exp (47 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (47 / 160 : ℝ) (1009221950051 / 1000000000000 : ℝ)
    (3353621249 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell235_rightExp :
    Real.exp (59 / 200 : ℝ) ≤ (13431263587 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (59 / 200 : ℝ) (504630686777 / 500000000000 : ℝ)
    (13431263587 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell235_denomUpper :
    Real.exp (41461188666074091 / 10000000000000000 : ℝ) ≤ (631882816237 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (41461188666074091 / 10000000000000000 : ℝ)
    (1138334483309 / 1000000000000 : ℝ) (631882816237 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell235_denomLower :
    (157090898101 / 2500000000 : ℝ) ≤ Real.exp (1293916835861051 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1293916835861051 / 312500000000000 : ℝ) (569067912997 /
    500000000000 : ℝ) (157090898101 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell235_product_lower :
    (1316963710861051 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (47 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell235_leftExp
    (by norm_num : (0 : ℝ) ≤ (3353621249 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell235_product_upper :
    Real.pi * Real.exp (59 / 200 : ℝ) ≤ (42195563666074091 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell235_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell235_endpointLower :
    (226283309 / 156250000 : ℝ) ≤ hpThetaTraceEndpointLower (47 / 320 : ℝ) (59 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1316963710861051 / 312500000000000 : ℝ) (Real.pi * Real.exp (47 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell235_product_lower
  have hD : Real.exp (Real.pi * Real.exp (59 / 200 : ℝ) - (47 / 640 : ℝ)) ≤
      (631882816237 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell235_denomUpper
    linarith [hpThetaJensenCell235_product_upper]
  have hi : (1 / (631882816237 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (59 / 200 : ℝ) - (47 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (631882816237 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (631882816237 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((47 / 640 : ℝ) - Real.pi * Real.exp (59 / 200 : ℝ)) := by
    rw [show (47 / 640 : ℝ) - Real.pi * Real.exp (59 / 200 : ℝ) =
      -(Real.pi * Real.exp (59 / 200 : ℝ) - (47 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (47 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (47 / 160 : ℝ)) := by
    have h := hpThetaJensenCell235_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (631882816237 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell235_endpointUpper :
    hpThetaJensenKernelEndpointUpper (47 / 320 : ℝ) (59 / 400 : ℝ) ≤ (3662065117 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (59 / 200 : ℝ)) (42195563666074091 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (59 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell235_product_upper
  have hD : (157090898101 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (47 / 160 : ℝ) - (59 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell235_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell235_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (47 / 160 : ℝ) - (59 / 800 : ℝ)) ≤
      (1 / (157090898101 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (157090898101 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((59 / 800 : ℝ) - Real.pi * Real.exp (47 / 160 : ℝ)) ≤
      (2 / (157090898101 / 2500000000 : ℝ) : ℝ) := by
    rw [show (59 / 800 : ℝ) - Real.pi * Real.exp (47 / 160 : ℝ) =
      -(Real.pi * Real.exp (47 / 160 : ℝ) - (59 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (42195563666074091 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (42195563666074091 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell235_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (47 / 320 : ℝ) (59 / 400 : ℝ)) :
    (226283309 / 156250000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3662065117 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell235_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell235_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell236_leftExp :
    (6715631793 / 5000000000 : ℝ) ≤ Real.exp (59 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (59 / 200 : ℝ) (1009261373553 / 1000000000000 : ℝ)
    (6715631793 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell236_rightExp :
    Real.exp (237 / 800 : ℝ) ≤ (2689612633 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (237 / 800 : ℝ) (1009300798597 / 1000000000000 : ℝ)
    (2689612633 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell236_denomUpper :
    Real.exp (8302168220544369 / 2000000000000000 : ℝ) ≤ (158757017603 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8302168220544369 / 2000000000000000 : ℝ) (1138511125391
    / 1000000000000 : ℝ) (158757017603 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell236_denomLower :
    (631487164489 / 10000000000 : ℝ) ≤ Real.exp (2590932826979307 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2590932826979307 / 625000000000000 : ℝ) (1138312202641 /
    1000000000000 : ℝ) (631487164489 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell236_product_lower :
    (2637221889479307 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (59 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell236_leftExp
    (by norm_num : (0 : ℝ) ≤ (6715631793 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell236_product_upper :
    Real.pi * Real.exp (237 / 800 : ℝ) ≤ (8449668220544369 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell236_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell236_endpointLower :
    (2891289401 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (59 / 400 : ℝ) (237 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2637221889479307 / 625000000000000 : ℝ) (Real.pi * Real.exp (59 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell236_product_lower
  have hD : Real.exp (Real.pi * Real.exp (237 / 800 : ℝ) - (59 / 800 : ℝ)) ≤
      (158757017603 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell236_denomUpper
    linarith [hpThetaJensenCell236_product_upper]
  have hi : (1 / (158757017603 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (237 / 800 : ℝ) - (59 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (158757017603 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (158757017603 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((59 / 800 : ℝ) - Real.pi * Real.exp (237 / 800 : ℝ)) := by
    rw [show (59 / 800 : ℝ) - Real.pi * Real.exp (237 / 800 : ℝ) =
      -(Real.pi * Real.exp (237 / 800 : ℝ) - (59 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (59 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (59 / 200 : ℝ)) := by
    have h := hpThetaJensenCell236_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (158757017603 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell236_endpointUpper :
    hpThetaJensenKernelEndpointUpper (59 / 400 : ℝ) (237 / 1600 : ℝ) ≤ (2924471589 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (237 / 800 : ℝ)) (8449668220544369 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (237 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell236_product_upper
  have hD : (631487164489 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (59 / 200 : ℝ) - (237 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell236_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell236_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (59 / 200 : ℝ) - (237 / 3200 : ℝ)) ≤
      (1 / (631487164489 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (631487164489 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((237 / 3200 : ℝ) - Real.pi * Real.exp (59 / 200 : ℝ)) ≤
      (2 / (631487164489 / 10000000000 : ℝ) : ℝ) := by
    rw [show (237 / 3200 : ℝ) - Real.pi * Real.exp (59 / 200 : ℝ) =
      -(Real.pi * Real.exp (59 / 200 : ℝ) - (237 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8449668220544369 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (8449668220544369 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell236_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (59 / 400 : ℝ) (237 / 1600 : ℝ)) :
    (2891289401 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2924471589 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell236_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell236_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell237_leftExp :
    (13448063163 / 10000000000 : ℝ) ≤ Real.exp (237 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (237 / 800 : ℝ) (252325199649 / 250000000000 : ℝ)
    (13448063163 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell237_rightExp :
    Real.exp (119 / 400 : ℝ) ≤ (6732441877 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (119 / 400 : ℝ) (1009340225179 / 1000000000000 : ℝ)
    (6732441877 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell237_denomUpper :
    Real.exp (20780279773690061 / 5000000000000000 : ℝ) ≤ (638193192939 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (20780279773690061 / 5000000000000000 : ℝ) (569344014883
    / 500000000000 : ℝ) (638193192939 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell237_denomLower :
    (126926089599 / 2000000000 : ℝ) ≤ Real.exp (5188072206046937 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5188072206046937 / 1250000000000000 : ℝ) (569244420597 /
    500000000000 : ℝ) (126926089599 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell237_product_lower :
    (5281040956046937 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (237 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell237_leftExp
    (by norm_num : (0 : ℝ) ≤ (13448063163 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell237_product_upper :
    Real.pi * Real.exp (119 / 400 : ℝ) ≤ (21150592273690061 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell237_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell237_endpointLower :
    (14430693239 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (237 / 1600 : ℝ) (119 / 800 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5281040956046937 / 1250000000000000 : ℝ) (Real.pi * Real.exp (237 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell237_product_lower
  have hD : Real.exp (Real.pi * Real.exp (119 / 400 : ℝ) - (237 / 3200 : ℝ)) ≤
      (638193192939 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell237_denomUpper
    linarith [hpThetaJensenCell237_product_upper]
  have hi : (1 / (638193192939 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (119 / 400 : ℝ) - (237 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (638193192939 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (638193192939 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((237 / 3200 : ℝ) - Real.pi * Real.exp (119 / 400 : ℝ)) := by
    rw [show (237 / 3200 : ℝ) - Real.pi * Real.exp (119 / 400 : ℝ) =
      -(Real.pi * Real.exp (119 / 400 : ℝ) - (237 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (237 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (237 / 800 : ℝ)) := by
    have h := hpThetaJensenCell237_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (638193192939 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell237_endpointUpper :
    hpThetaJensenKernelEndpointUpper (237 / 1600 : ℝ) (119 / 800 : ℝ) ≤ (14596385517 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (119 / 400 : ℝ)) (21150592273690061 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (119 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell237_product_upper
  have hD : (126926089599 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (237 / 800 : ℝ) - (119 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell237_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell237_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (237 / 800 : ℝ) - (119 / 1600 : ℝ)) ≤
      (1 / (126926089599 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (126926089599 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((119 / 1600 : ℝ) - Real.pi * Real.exp (237 / 800 : ℝ)) ≤
      (2 / (126926089599 / 2000000000 : ℝ) : ℝ) := by
    rw [show (119 / 1600 : ℝ) - Real.pi * Real.exp (237 / 800 : ℝ) =
      -(Real.pi * Real.exp (237 / 800 : ℝ) - (119 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (21150592273690061 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (21150592273690061 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell237_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (237 / 1600 : ℝ) (119 / 800 : ℝ)) :
    (14430693239 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (14596385517 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell237_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell237_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell238_leftExp :
    (13464883753 / 10000000000 : ℝ) ≤ Real.exp (119 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (119 / 400 : ℝ) (504670112589 / 500000000000 : ℝ)
    (13464883753 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell238_rightExp :
    Real.exp (239 / 800 : ℝ) ≤ (13481725383 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (239 / 800 : ℝ) (504689826651 / 500000000000 : ℝ)
    (13481725383 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell238_denomUpper :
    Real.exp (41610344091155119 / 10000000000000000 : ℝ) ≤ (32068916529 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (41610344091155119 / 10000000000000000 : ℝ) (142358149609
    / 125000000000 : ℝ) (32068916529 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell238_denomLower :
    (127558717563 / 2000000000 : ℝ) ≤ Real.exp (5194287009919347 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5194287009919347 / 1250000000000000 : ℝ) (569332871029 /
    500000000000 : ℝ) (127558717563 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell238_product_lower :
    (5287646384919347 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (119 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell238_leftExp
    (by norm_num : (0 : ℝ) ≤ (13464883753 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell238_product_upper :
    Real.pi * Real.exp (239 / 800 : ℝ) ≤ (42354094091155119 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell238_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell238_endpointLower :
    (14404870927 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (119 / 800 : ℝ) (239 / 1600 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5287646384919347 / 1250000000000000 : ℝ) (Real.pi * Real.exp (119 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell238_product_lower
  have hD : Real.exp (Real.pi * Real.exp (239 / 800 : ℝ) - (119 / 1600 : ℝ)) ≤
      (32068916529 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell238_denomUpper
    linarith [hpThetaJensenCell238_product_upper]
  have hi : (1 / (32068916529 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (239 / 800 : ℝ) - (119 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (32068916529 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (32068916529 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((119 / 1600 : ℝ) - Real.pi * Real.exp (239 / 800 : ℝ)) := by
    rw [show (119 / 1600 : ℝ) - Real.pi * Real.exp (239 / 800 : ℝ) =
      -(Real.pi * Real.exp (239 / 800 : ℝ) - (119 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (119 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (119 / 400 : ℝ)) := by
    have h := hpThetaJensenCell238_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (32068916529 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell238_endpointUpper :
    hpThetaJensenKernelEndpointUpper (119 / 800 : ℝ) (239 / 1600 : ℝ) ≤ (7285171829 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (239 / 800 : ℝ)) (42354094091155119 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (239 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell238_product_upper
  have hD : (127558717563 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (119 / 400 : ℝ) - (239 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell238_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell238_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (119 / 400 : ℝ) - (239 / 3200 : ℝ)) ≤
      (1 / (127558717563 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (127558717563 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((239 / 3200 : ℝ) - Real.pi * Real.exp (119 / 400 : ℝ)) ≤
      (2 / (127558717563 / 2000000000 : ℝ) : ℝ) := by
    rw [show (239 / 3200 : ℝ) - Real.pi * Real.exp (119 / 400 : ℝ) =
      -(Real.pi * Real.exp (119 / 400 : ℝ) - (239 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (42354094091155119 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (42354094091155119 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell238_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (119 / 800 : ℝ) (239 / 1600 : ℝ)) :
    (14404870927 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7285171829 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell238_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell238_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell239_leftExp :
    (13481725381 / 10000000000 : ℝ) ≤ Real.exp (239 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (239 / 800 : ℝ) (1009379653301 / 1000000000000 : ℝ)
    (13481725381 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell239_rightExp :
    Real.exp (3 / 10 : ℝ) ≤ (13498588077 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3 / 10 : ℝ) (201883816593 / 200000000000 : ℝ)
    (13498588077 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell239_denomUpper :
    Real.exp (41660194812586661 / 10000000000000000 : ℝ) ≤ (322291815263 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (41660194812586661 / 10000000000000000 : ℝ) (35595082097
    / 31250000000 : ℝ) (322291815263 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell239_denomLower :
    (160244182449 / 2500000000 : ℝ) ≤ Real.exp (5200510075393319 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5200510075393319 / 1250000000000000 : ℝ) (1822148649 /
    1600000000 : ℝ) (160244182449 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell239_product_lower :
    (5294260075393319 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (239 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell239_leftExp
    (by norm_num : (0 : ℝ) ≤ (13481725381 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell239_product_upper :
    Real.pi * Real.exp (3 / 10 : ℝ) ≤ (42407069812586661 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell239_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell239_endpointLower :
    (1797372567 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (239 / 1600 : ℝ) (3 / 20 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5294260075393319 / 1250000000000000 : ℝ) (Real.pi * Real.exp (239 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell239_product_lower
  have hD : Real.exp (Real.pi * Real.exp (3 / 10 : ℝ) - (239 / 3200 : ℝ)) ≤
      (322291815263 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell239_denomUpper
    linarith [hpThetaJensenCell239_product_upper]
  have hi : (1 / (322291815263 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (3 / 10 : ℝ) - (239 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (322291815263 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (322291815263 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((239 / 3200 : ℝ) - Real.pi * Real.exp (3 / 10 : ℝ)) := by
    rw [show (239 / 3200 : ℝ) - Real.pi * Real.exp (3 / 10 : ℝ) =
      -(Real.pi * Real.exp (3 / 10 : ℝ) - (239 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (239 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (239 / 800 : ℝ)) := by
    have h := hpThetaJensenCell239_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (322291815263 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell239_endpointUpper :
    hpThetaJensenKernelEndpointUpper (239 / 1600 : ℝ) (3 / 20 : ℝ) ≤ (7272116419 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (3 / 10 : ℝ)) (42407069812586661 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (3 / 20 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell239_product_upper
  have hD : (160244182449 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (239 / 800 : ℝ) - (3 / 40 : ℝ)) := by
    apply le_trans hpThetaJensenCell239_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell239_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (239 / 800 : ℝ) - (3 / 40 : ℝ)) ≤
      (1 / (160244182449 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (160244182449 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((3 / 40 : ℝ) - Real.pi * Real.exp (239 / 800 : ℝ)) ≤
      (2 / (160244182449 / 2500000000 : ℝ) : ℝ) := by
    rw [show (3 / 40 : ℝ) - Real.pi * Real.exp (239 / 800 : ℝ) =
      -(Real.pi * Real.exp (239 / 800 : ℝ) - (3 / 40 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (42407069812586661 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (42407069812586661 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell239_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (239 / 1600 : ℝ) (3 / 20 : ℝ)) :
    (1797372567 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7272116419 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell239_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell239_endpointUpper

def hpThetaJensenCellsBatch011Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (594352419 / 400000000 : ℝ)
  | 1 => (14834215747 / 10000000000 : ℝ)
  | 2 => (1851193147 / 1250000000 : ℝ)
  | 3 => (1478479921 / 1000000000 : ℝ)
  | 4 => (14759978301 / 10000000000 : ℝ)
  | 5 => (14735082899 / 10000000000 : ℝ)
  | 6 => (7355056729 / 5000000000 : ℝ)
  | 7 => (458908451 / 312500000 : ℝ)
  | 8 => (14659954271 / 10000000000 : ℝ)
  | 9 => (2926953087 / 2000000000 : ℝ)
  | 10 => (14609504373 / 10000000000 : ℝ)
  | 11 => (3646042887 / 2500000000 : ℝ)
  | 12 => (14558767417 / 10000000000 : ℝ)
  | 13 => (7266646219 / 5000000000 : ℝ)
  | 14 => (3626936767 / 2500000000 : ℝ)
  | 15 => (226283309 / 156250000 : ℝ)
  | 16 => (2891289401 / 2000000000 : ℝ)
  | 17 => (14430693239 / 10000000000 : ℝ)
  | 18 => (14404870927 / 10000000000 : ℝ)
  | 19 => (1797372567 / 1250000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch011Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (15028096263 / 10000000000 : ℝ)
  | 1 => (15003297549 / 10000000000 : ℝ)
  | 2 => (3744605513 / 2500000000 : ℝ)
  | 3 => (7476735113 / 5000000000 : ℝ)
  | 4 => (14928442523 / 10000000000 : ℝ)
  | 5 => (14903339397 / 10000000000 : ℝ)
  | 6 => (1859770163 / 1250000000 : ℝ)
  | 7 => (7426454347 / 5000000000 : ℝ)
  | 8 => (3706895509 / 2500000000 : ℝ)
  | 9 => (592087271 / 400000000 : ℝ)
  | 10 => (14776708381 / 10000000000 : ℝ)
  | 11 => (1475116231 / 1000000000 : ℝ)
  | 12 => (920346501 / 625000000 : ℝ)
  | 13 => (7349926987 / 5000000000 : ℝ)
  | 14 => (14674092637 / 10000000000 : ℝ)
  | 15 => (3662065117 / 2500000000 : ℝ)
  | 16 => (2924471589 / 2000000000 : ℝ)
  | 17 => (14596385517 / 10000000000 : ℝ)
  | 18 => (7285171829 / 5000000000 : ℝ)
  | 19 => (7272116419 / 5000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch011_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((220 : ℝ) + (j.val : ℝ)) / 1600)
      (((220 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch011Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch011Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell220_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell221_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell222_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell223_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell224_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell225_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell226_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell227_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell228_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell229_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell230_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell231_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell232_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell233_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell234_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell235_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell236_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell237_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell238_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell239_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper] at h ⊢
    exact h

end HodgeProofHP
