import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell180_leftExp :
    (12523227161 / 10000000000 : ℝ) ≤ Real.exp (9 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9 / 40 : ℝ) (40282241091 / 40000000000 : ℝ) (12523227161
    / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell180_rightExp :
    Real.exp (181 / 800 : ℝ) ≤ (1567361373 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (181 / 800 : ℝ) (1007095366171 / 1000000000000 : ℝ)
    (1567361373 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell180_denomUpper :
    Real.exp (4853699017887189 / 1250000000000000 : ℝ) ≤ (6070965617 / 125000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4853699017887189 / 1250000000000000 : ℝ) (225802300977 /
    200000000000 : ℝ) (6070965617 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell180_denomLower :
    (483141523131 / 10000000000 : ℝ) ≤ Real.exp (4847155657897539 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4847155657897539 / 1250000000000000 : ℝ) (1128826831771
    / 1000000000000 : ℝ) (483141523131 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell180_product_lower :
    (4917858782897539 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (9 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell180_leftExp
    (by norm_num : (0 : ℝ) ≤ (12523227161 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell180_product_upper :
    Real.pi * Real.exp (181 / 800 : ℝ) ≤ (4924011517887189 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell180_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell180_endpointLower :
    (3155077617 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (9 / 80 : ℝ) (181 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4917858782897539 / 1250000000000000 : ℝ) (Real.pi * Real.exp (9 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell180_product_lower
  have hD : Real.exp (Real.pi * Real.exp (181 / 800 : ℝ) - (9 / 160 : ℝ)) ≤
      (6070965617 / 125000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell180_denomUpper
    linarith [hpThetaJensenCell180_product_upper]
  have hi : (1 / (6070965617 / 125000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (181 / 800 : ℝ) - (9 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (6070965617 / 125000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (6070965617 / 125000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((9 / 160 : ℝ) - Real.pi * Real.exp (181 / 800 : ℝ)) := by
    rw [show (9 / 160 : ℝ) - Real.pi * Real.exp (181 / 800 : ℝ) =
      -(Real.pi * Real.exp (181 / 800 : ℝ) - (9 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (9 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (9 / 40 : ℝ)) := by
    have h := hpThetaJensenCell180_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (6070965617 / 125000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell180_endpointUpper :
    hpThetaJensenKernelEndpointUpper (9 / 80 : ℝ) (181 / 1600 : ℝ) ≤ (1994003693 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (181 / 800 : ℝ)) (4924011517887189 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (181 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell180_product_upper
  have hD : (483141523131 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (9 / 40 : ℝ) - (181 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell180_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell180_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (9 / 40 : ℝ) - (181 / 3200 : ℝ)) ≤
      (1 / (483141523131 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (483141523131 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((181 / 3200 : ℝ) - Real.pi * Real.exp (9 / 40 : ℝ)) ≤
      (2 / (483141523131 / 10000000000 : ℝ) : ℝ) := by
    rw [show (181 / 3200 : ℝ) - Real.pi * Real.exp (9 / 40 : ℝ) =
      -(Real.pi * Real.exp (9 / 40 : ℝ) - (181 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4924011517887189 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (4924011517887189 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell180_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (9 / 80 : ℝ) (181 / 1600 : ℝ)) :
    (3155077617 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1994003693 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell180_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell180_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell181_leftExp :
    (12538890983 / 10000000000 : ℝ) ≤ Real.exp (181 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (181 / 800 : ℝ) (100709536617 / 100000000000 : ℝ)
    (12538890983 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell181_rightExp :
    Real.exp (91 / 400 : ℝ) ≤ (6277287199 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (91 / 400 : ℝ) (503567353301 / 500000000000 : ℝ)
    (6277287199 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell181_denomUpper :
    Real.exp (19437869023368007 / 5000000000000000 : ℝ) ≤ (487923629991 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (19437869023368007 / 5000000000000000 : ℝ) (2822935817 /
    2500000000 : ℝ) (487923629991 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell181_denomLower :
    (485373187147 / 10000000000 : ℝ) ≤ Real.exp (4852916200133117 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4852916200133117 / 1250000000000000 : ℝ) (282247352461 /
    250000000000 : ℝ) (485373187147 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell181_product_lower :
    (4924009950133117 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (181 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell181_leftExp
    (by norm_num : (0 : ℝ) ≤ (12538890983 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell181_product_upper :
    Real.pi * Real.exp (91 / 400 : ℝ) ≤ (19720681523368007 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell181_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell181_endpointLower :
    (3150836507 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (181 / 1600 : ℝ) (91 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4924009950133117 / 1250000000000000 : ℝ) (Real.pi * Real.exp (181 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell181_product_lower
  have hD : Real.exp (Real.pi * Real.exp (91 / 400 : ℝ) - (181 / 3200 : ℝ)) ≤
      (487923629991 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell181_denomUpper
    linarith [hpThetaJensenCell181_product_upper]
  have hi : (1 / (487923629991 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (91 / 400 : ℝ) - (181 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (487923629991 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (487923629991 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((181 / 3200 : ℝ) - Real.pi * Real.exp (91 / 400 : ℝ)) := by
    rw [show (181 / 3200 : ℝ) - Real.pi * Real.exp (91 / 400 : ℝ) =
      -(Real.pi * Real.exp (91 / 400 : ℝ) - (181 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (181 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (181 / 800 : ℝ)) := by
    have h := hpThetaJensenCell181_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (487923629991 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell181_endpointUpper :
    hpThetaJensenKernelEndpointUpper (181 / 1600 : ℝ) (91 / 800 : ℝ) ≤ (15930659901 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (91 / 400 : ℝ)) (19720681523368007 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (91 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell181_product_upper
  have hD : (485373187147 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (181 / 800 : ℝ) - (91 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell181_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell181_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (181 / 800 : ℝ) - (91 / 1600 : ℝ)) ≤
      (1 / (485373187147 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (485373187147 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((91 / 1600 : ℝ) - Real.pi * Real.exp (181 / 800 : ℝ)) ≤
      (2 / (485373187147 / 10000000000 : ℝ) : ℝ) := by
    rw [show (91 / 1600 : ℝ) - Real.pi * Real.exp (181 / 800 : ℝ) =
      -(Real.pi * Real.exp (181 / 800 : ℝ) - (91 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (19720681523368007 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (19720681523368007 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell181_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (181 / 1600 : ℝ) (91 / 800 : ℝ)) :
    (3150836507 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15930659901 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell181_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell181_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell182_leftExp :
    (12554574397 / 10000000000 : ℝ) ≤ Real.exp (91 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (91 / 400 : ℝ) (1007134706601 / 1000000000000 : ℝ)
    (12554574397 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell182_rightExp :
    Real.exp (183 / 800 : ℝ) ≤ (12570277429 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (183 / 800 : ℝ) (100717404857 / 100000000000 : ℝ)
    (12570277429 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell182_denomUpper :
    Real.exp (38921945579004397 / 10000000000000000 : ℝ) ≤ (490183421627 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (38921945579004397 / 10000000000000000 : ℝ) (225867477939
    / 200000000000 : ℝ) (490183421627 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell182_denomLower :
    (243809080323 / 5000000000 : ℝ) ≤ Real.exp (4858684436127503 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4858684436127503 / 1250000000000000 : ℝ) (1129152228517
    / 1000000000000 : ℝ) (243809080323 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell182_product_lower :
    (4930168811127503 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (91 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell182_leftExp
    (by norm_num : (0 : ℝ) ≤ (12554574397 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell182_product_upper :
    Real.pi * Real.exp (183 / 800 : ℝ) ≤ (39490695579004397 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell182_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell182_endpointLower :
    (3933221029 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (91 / 800 : ℝ) (183 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4930168811127503 / 1250000000000000 : ℝ) (Real.pi * Real.exp (91 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell182_product_lower
  have hD : Real.exp (Real.pi * Real.exp (183 / 800 : ℝ) - (91 / 1600 : ℝ)) ≤
      (490183421627 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell182_denomUpper
    linarith [hpThetaJensenCell182_product_upper]
  have hi : (1 / (490183421627 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (183 / 800 : ℝ) - (91 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (490183421627 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (490183421627 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((91 / 1600 : ℝ) - Real.pi * Real.exp (183 / 800 : ℝ)) := by
    rw [show (91 / 1600 : ℝ) - Real.pi * Real.exp (183 / 800 : ℝ) =
      -(Real.pi * Real.exp (183 / 800 : ℝ) - (91 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (91 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (91 / 400 : ℝ)) := by
    have h := hpThetaJensenCell182_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (490183421627 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell182_endpointUpper :
    hpThetaJensenKernelEndpointUpper (91 / 800 : ℝ) (183 / 1600 : ℝ) ≤ (15909196347 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (183 / 800 : ℝ)) (39490695579004397 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (183 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell182_product_upper
  have hD : (243809080323 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (91 / 400 : ℝ) - (183 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell182_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell182_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (91 / 400 : ℝ) - (183 / 3200 : ℝ)) ≤
      (1 / (243809080323 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (243809080323 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((183 / 3200 : ℝ) - Real.pi * Real.exp (91 / 400 : ℝ)) ≤
      (2 / (243809080323 / 5000000000 : ℝ) : ℝ) := by
    rw [show (183 / 3200 : ℝ) - Real.pi * Real.exp (91 / 400 : ℝ) =
      -(Real.pi * Real.exp (91 / 400 : ℝ) - (183 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (39490695579004397 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (39490695579004397 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell182_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (91 / 800 : ℝ) (183 / 1600 : ℝ)) :
    (3933221029 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15909196347 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell182_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell182_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell183_leftExp :
    (12570277427 / 10000000000 : ℝ) ≤ Real.exp (183 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (183 / 800 : ℝ) (1007174048569 / 1000000000000 : ℝ)
    (12570277427 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell183_rightExp :
    Real.exp (23 / 100 : ℝ) ≤ (125860001 / 100000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (23 / 100 : ℝ) (40288535683 / 40000000000 : ℝ)
    (125860001 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell183_denomUpper :
    Real.exp (389682148121593 / 100000000000000 : ℝ) ≤ (492456717861 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (389682148121593 / 100000000000000 : ℝ) (1129500693923 /
    1000000000000 : ℝ) (492456717861 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell183_denomLower :
    (48987653659 / 1000000000 : ℝ) ≤ Real.exp (4864460375305473 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4864460375305473 / 1250000000000000 : ℝ) (564657644077 /
    500000000000 : ℝ) (48987653659 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell183_product_lower :
    (4936335375305473 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (183 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell183_leftExp
    (by norm_num : (0 : ℝ) ≤ (12570277427 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell183_product_upper :
    Real.pi * Real.exp (23 / 100 : ℝ) ≤ (395400898121593 / 100000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell183_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell183_endpointLower :
    (3927873309 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (183 / 1600 : ℝ) (23 / 200 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4936335375305473 / 1250000000000000 : ℝ) (Real.pi * Real.exp (183 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell183_product_lower
  have hD : Real.exp (Real.pi * Real.exp (23 / 100 : ℝ) - (183 / 3200 : ℝ)) ≤
      (492456717861 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell183_denomUpper
    linarith [hpThetaJensenCell183_product_upper]
  have hi : (1 / (492456717861 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (23 / 100 : ℝ) - (183 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (492456717861 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (492456717861 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((183 / 3200 : ℝ) - Real.pi * Real.exp (23 / 100 : ℝ)) := by
    rw [show (183 / 3200 : ℝ) - Real.pi * Real.exp (23 / 100 : ℝ) =
      -(Real.pi * Real.exp (23 / 100 : ℝ) - (183 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (183 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (183 / 800 : ℝ)) := by
    have h := hpThetaJensenCell183_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (492456717861 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell183_endpointUpper :
    hpThetaJensenKernelEndpointUpper (183 / 1600 : ℝ) (23 / 200 : ℝ) ≤ (7943819641 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (23 / 100 : ℝ)) (395400898121593 / 100000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (23 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell183_product_upper
  have hD : (48987653659 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (183 / 800 : ℝ) - (23 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell183_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell183_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (183 / 800 : ℝ) - (23 / 400 : ℝ)) ≤
      (1 / (48987653659 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (48987653659 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((23 / 400 : ℝ) - Real.pi * Real.exp (183 / 800 : ℝ)) ≤
      (2 / (48987653659 / 1000000000 : ℝ) : ℝ) := by
    rw [show (23 / 400 : ℝ) - Real.pi * Real.exp (183 / 800 : ℝ) =
      -(Real.pi * Real.exp (183 / 800 : ℝ) - (23 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (395400898121593 / 100000000000000 : ℝ) ^ 2 - 6 *
      (395400898121593 / 100000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell183_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (183 / 1600 : ℝ) (23 / 200 : ℝ)) :
    (3927873309 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7943819641 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell183_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell183_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell184_leftExp :
    (12586000099 / 10000000000 : ℝ) ≤ Real.exp (23 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (23 / 100 : ℝ) (503606696037 / 500000000000 : ℝ)
    (12586000099 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell184_rightExp :
    Real.exp (37 / 160 : ℝ) ≤ (12601742437 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (37 / 160 : ℝ) (251813184279 / 250000000000 : ℝ)
    (12601742437 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell184_denomUpper :
    Real.exp (39014545827882141 / 10000000000000000 : ℝ) ≤ (61842951683 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (39014545827882141 / 10000000000000000 : ℝ)
    (1129664239869 / 1000000000000 : ℝ) (61842951683 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell184_denomLower :
    (246074204493 / 5000000000 : ℝ) ≤ Real.exp (4870244027877201 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4870244027877201 / 1250000000000000 : ℝ) (564739294571 /
    500000000000 : ℝ) (246074204493 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell184_product_lower :
    (4942509652877201 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (23 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell184_leftExp
    (by norm_num : (0 : ℝ) ≤ (12586000099 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell184_product_upper :
    Real.pi * Real.exp (37 / 160 : ℝ) ≤ (39589545827882141 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell184_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell184_endpointLower :
    (15690010293 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (23 / 200 : ℝ) (37 / 320 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4942509652877201 / 1250000000000000 : ℝ) (Real.pi * Real.exp (23 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell184_product_lower
  have hD : Real.exp (Real.pi * Real.exp (37 / 160 : ℝ) - (23 / 400 : ℝ)) ≤
      (61842951683 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell184_denomUpper
    linarith [hpThetaJensenCell184_product_upper]
  have hi : (1 / (61842951683 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (37 / 160 : ℝ) - (23 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (61842951683 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (61842951683 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((23 / 400 : ℝ) - Real.pi * Real.exp (37 / 160 : ℝ)) := by
    rw [show (23 / 400 : ℝ) - Real.pi * Real.exp (37 / 160 : ℝ) =
      -(Real.pi * Real.exp (37 / 160 : ℝ) - (23 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (23 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (23 / 100 : ℝ)) := by
    have h := hpThetaJensenCell184_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (61842951683 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell184_endpointUpper :
    hpThetaJensenKernelEndpointUpper (23 / 200 : ℝ) (37 / 320 : ℝ) ≤ (15865989107 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (37 / 160 : ℝ)) (39589545827882141 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (37 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell184_product_upper
  have hD : (246074204493 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (23 / 100 : ℝ) - (37 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell184_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell184_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (23 / 100 : ℝ) - (37 / 640 : ℝ)) ≤
      (1 / (246074204493 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (246074204493 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((37 / 640 : ℝ) - Real.pi * Real.exp (23 / 100 : ℝ)) ≤
      (2 / (246074204493 / 5000000000 : ℝ) : ℝ) := by
    rw [show (37 / 640 : ℝ) - Real.pi * Real.exp (23 / 100 : ℝ) =
      -(Real.pi * Real.exp (23 / 100 : ℝ) - (37 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (39589545827882141 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (39589545827882141 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell184_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (23 / 200 : ℝ) (37 / 320 : ℝ)) :
    (15690010293 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15865989107 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell184_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell184_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell185_leftExp :
    (3150435609 / 2500000000 : ℝ) ≤ Real.exp (37 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (37 / 160 : ℝ) (201450547423 / 200000000000 : ℝ)
    (3150435609 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell185_rightExp :
    Real.exp (93 / 400 : ℝ) ≤ (788594029 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (93 / 400 : ℝ) (201458416739 / 200000000000 : ℝ)
    (788594029 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell185_denomUpper :
    Real.exp (2441308668848197 / 625000000000000 : ℝ) ≤ (124261050921 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (2441308668848197 / 625000000000000 : ℝ) (1129828027899 /
    1000000000000 : ℝ) (124261050921 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell185_denomLower :
    (494433872073 / 10000000000 : ℝ) ≤ Real.exp (1219008850718691 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1219008850718691 / 312500000000000 : ℝ) (141205266479 /
    125000000000 : ℝ) (494433872073 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell185_product_lower :
    (1237172913218691 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (37 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell185_leftExp
    (by norm_num : (0 : ℝ) ≤ (3150435609 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell185_product_upper :
    Real.pi * Real.exp (93 / 400 : ℝ) ≤ (2477441481348197 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell185_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell185_endpointLower :
    (1958554461 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (37 / 320 : ℝ) (93 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1237172913218691 / 312500000000000 : ℝ) (Real.pi * Real.exp (37 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell185_product_lower
  have hD : Real.exp (Real.pi * Real.exp (93 / 400 : ℝ) - (37 / 640 : ℝ)) ≤
      (124261050921 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell185_denomUpper
    linarith [hpThetaJensenCell185_product_upper]
  have hi : (1 / (124261050921 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (93 / 400 : ℝ) - (37 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (124261050921 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (124261050921 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((37 / 640 : ℝ) - Real.pi * Real.exp (93 / 400 : ℝ)) := by
    rw [show (37 / 640 : ℝ) - Real.pi * Real.exp (93 / 400 : ℝ) =
      -(Real.pi * Real.exp (93 / 400 : ℝ) - (37 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (37 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (37 / 160 : ℝ)) := by
    have h := hpThetaJensenCell185_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (124261050921 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell185_endpointUpper :
    hpThetaJensenKernelEndpointUpper (37 / 320 : ℝ) (93 / 800 : ℝ) ≤ (3168849247 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (93 / 400 : ℝ)) (2477441481348197 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (93 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell185_product_upper
  have hD : (494433872073 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (37 / 160 : ℝ) - (93 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell185_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell185_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (37 / 160 : ℝ) - (93 / 1600 : ℝ)) ≤
      (1 / (494433872073 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (494433872073 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((93 / 1600 : ℝ) - Real.pi * Real.exp (37 / 160 : ℝ)) ≤
      (2 / (494433872073 / 10000000000 : ℝ) : ℝ) := by
    rw [show (93 / 1600 : ℝ) - Real.pi * Real.exp (37 / 160 : ℝ) =
      -(Real.pi * Real.exp (37 / 160 : ℝ) - (93 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2477441481348197 / 625000000000000 : ℝ) ^ 2 - 6 *
      (2477441481348197 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell185_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (37 / 320 : ℝ) (93 / 800 : ℝ)) :
    (1958554461 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3168849247 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell185_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell185_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell186_leftExp :
    (12617504463 / 10000000000 : ℝ) ≤ Real.exp (93 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (93 / 400 : ℝ) (503646041847 / 500000000000 : ℝ)
    (12617504463 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell186_rightExp :
    Real.exp (187 / 800 : ℝ) ≤ (6316643103 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (187 / 800 : ℝ) (100733143181 / 100000000000 : ℝ)
    (6316643103 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell186_denomUpper :
    Real.exp (19553696755883079 / 5000000000000000 : ℝ) ≤ (249679292321 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (19553696755883079 / 5000000000000000 : ℝ) (282498014597
    / 250000000000 : ℝ) (249679292321 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell186_denomLower :
    (496733021193 / 10000000000 : ℝ) ≤ Real.exp (4881834510115637 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4881834510115637 / 1250000000000000 : ℝ) (1129805916601
    / 1000000000000 : ℝ) (496733021193 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell186_product_lower :
    (4954881385115637 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (93 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell186_leftExp
    (by norm_num : (0 : ℝ) ≤ (12617504463 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell186_product_upper :
    Real.pi * Real.exp (187 / 800 : ℝ) ≤ (19844321755883079 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell186_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell186_endpointLower :
    (15646769827 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (93 / 800 : ℝ) (187 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4954881385115637 / 1250000000000000 : ℝ) (Real.pi * Real.exp (93 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell186_product_lower
  have hD : Real.exp (Real.pi * Real.exp (187 / 800 : ℝ) - (93 / 1600 : ℝ)) ≤
      (249679292321 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell186_denomUpper
    linarith [hpThetaJensenCell186_product_upper]
  have hi : (1 / (249679292321 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (187 / 800 : ℝ) - (93 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (249679292321 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (249679292321 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((93 / 1600 : ℝ) - Real.pi * Real.exp (187 / 800 : ℝ)) := by
    rw [show (93 / 1600 : ℝ) - Real.pi * Real.exp (187 / 800 : ℝ) =
      -(Real.pi * Real.exp (187 / 800 : ℝ) - (93 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (93 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (93 / 400 : ℝ)) := by
    have h := hpThetaJensenCell186_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (249679292321 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell186_endpointUpper :
    hpThetaJensenKernelEndpointUpper (93 / 800 : ℝ) (187 / 1600 : ℝ) ≤ (247225173 / 156250000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (187 / 800 : ℝ)) (19844321755883079 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (187 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell186_product_upper
  have hD : (496733021193 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (93 / 400 : ℝ) - (187 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell186_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell186_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (93 / 400 : ℝ) - (187 / 3200 : ℝ)) ≤
      (1 / (496733021193 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (496733021193 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((187 / 3200 : ℝ) - Real.pi * Real.exp (93 / 400 : ℝ)) ≤
      (2 / (496733021193 / 10000000000 : ℝ) : ℝ) := by
    rw [show (187 / 3200 : ℝ) - Real.pi * Real.exp (93 / 400 : ℝ) =
      -(Real.pi * Real.exp (93 / 400 : ℝ) - (187 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (19844321755883079 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (19844321755883079 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell186_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (93 / 800 : ℝ) (187 / 1600 : ℝ)) :
    (15646769827 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (247225173 / 156250000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell186_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell186_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell187_leftExp :
    (2526657241 / 2000000000 : ℝ) ≤ Real.exp (187 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (187 / 800 : ℝ) (1007331431809 / 1000000000000 : ℝ)
    (2526657241 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell187_rightExp :
    Real.exp (47 / 200 : ℝ) ≤ (1581135961 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (47 / 200 : ℝ) (1007370781463 / 1000000000000 : ℝ)
    (1581135961 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell187_denomUpper :
    Real.exp (4894238792125873 / 1250000000000000 : ℝ) ≤ (501686853239 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4894238792125873 / 1250000000000000 : ℝ) (1130156331713
    / 1000000000000 : ℝ) (501686853239 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell187_denomLower :
    (249522976203 / 5000000000 : ℝ) ≤ Real.exp (977528271883459 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (977528271883459 / 250000000000000 : ℝ) (70623121489 /
    62500000000 : ℝ) (249522976203 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell187_product_lower :
    (992215771883459 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (187 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell187_leftExp
    (by norm_num : (0 : ℝ) ≤ (2526657241 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell187_product_upper :
    Real.pi * Real.exp (47 / 200 : ℝ) ≤ (4967285667125873 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell187_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell187_endpointLower :
    (7812506557 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (187 / 1600 : ℝ) (47 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (992215771883459 / 250000000000000 : ℝ) (Real.pi * Real.exp (187 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell187_product_lower
  have hD : Real.exp (Real.pi * Real.exp (47 / 200 : ℝ) - (187 / 3200 : ℝ)) ≤
      (501686853239 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell187_denomUpper
    linarith [hpThetaJensenCell187_product_upper]
  have hi : (1 / (501686853239 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (47 / 200 : ℝ) - (187 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (501686853239 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (501686853239 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((187 / 3200 : ℝ) - Real.pi * Real.exp (47 / 200 : ℝ)) := by
    rw [show (187 / 3200 : ℝ) - Real.pi * Real.exp (47 / 200 : ℝ) =
      -(Real.pi * Real.exp (47 / 200 : ℝ) - (187 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (187 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (187 / 800 : ℝ)) := by
    have h := hpThetaJensenCell187_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (501686853239 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell187_endpointUpper :
    hpThetaJensenKernelEndpointUpper (187 / 1600 : ℝ) (47 / 400 : ℝ) ≤ (632019361 / 400000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (47 / 200 : ℝ)) (4967285667125873 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (47 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell187_product_upper
  have hD : (249522976203 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (187 / 800 : ℝ) - (47 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell187_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell187_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (187 / 800 : ℝ) - (47 / 800 : ℝ)) ≤
      (1 / (249522976203 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (249522976203 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((47 / 800 : ℝ) - Real.pi * Real.exp (187 / 800 : ℝ)) ≤
      (2 / (249522976203 / 5000000000 : ℝ) : ℝ) := by
    rw [show (47 / 800 : ℝ) - Real.pi * Real.exp (187 / 800 : ℝ) =
      -(Real.pi * Real.exp (187 / 800 : ℝ) - (47 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4967285667125873 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (4967285667125873 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell187_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (187 / 1600 : ℝ) (47 / 400 : ℝ)) :
    (7812506557 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (632019361 / 400000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell187_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell187_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell188_leftExp :
    (12649087687 / 10000000000 : ℝ) ≤ Real.exp (47 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (47 / 200 : ℝ) (503685390731 / 500000000000 : ℝ)
    (12649087687 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell188_rightExp :
    Real.exp (189 / 800 : ℝ) ≤ (6332454467 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (189 / 800 : ℝ) (1007410132653 / 1000000000000 : ℝ)
    (6332454467 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell188_denomUpper :
    Real.exp (19600244626345931 / 5000000000000000 : ℝ) ≤ (25201455347 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (19600244626345931 / 5000000000000000 : ℝ) (1130320848237
    / 1000000000000 : ℝ) (25201455347 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell188_denomLower :
    (250686381277 / 5000000000 : ℝ) ≤ Real.exp (4893455960597213 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4893455960597213 / 1250000000000000 : ℝ) (565067106939 /
    500000000000 : ℝ) (250686381277 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell188_product_lower :
    (4967284085597213 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (47 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell188_leftExp
    (by norm_num : (0 : ℝ) ≤ (12649087687 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell188_product_upper :
    Real.pi * Real.exp (189 / 800 : ℝ) ≤ (19893994626345931 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell188_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell188_endpointLower :
    (7801582981 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (47 / 400 : ℝ) (189 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4967284085597213 / 1250000000000000 : ℝ) (Real.pi * Real.exp (47 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell188_product_lower
  have hD : Real.exp (Real.pi * Real.exp (189 / 800 : ℝ) - (47 / 800 : ℝ)) ≤
      (25201455347 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell188_denomUpper
    linarith [hpThetaJensenCell188_product_upper]
  have hi : (1 / (25201455347 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (189 / 800 : ℝ) - (47 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (25201455347 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (25201455347 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((47 / 800 : ℝ) - Real.pi * Real.exp (189 / 800 : ℝ)) := by
    rw [show (47 / 800 : ℝ) - Real.pi * Real.exp (189 / 800 : ℝ) =
      -(Real.pi * Real.exp (189 / 800 : ℝ) - (47 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (47 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (47 / 200 : ℝ)) := by
    have h := hpThetaJensenCell188_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (25201455347 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell188_endpointUpper :
    hpThetaJensenKernelEndpointUpper (47 / 400 : ℝ) (189 / 1600 : ℝ) ≤ (15778465501 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (189 / 800 : ℝ)) (19893994626345931 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (189 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell188_product_upper
  have hD : (250686381277 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (47 / 200 : ℝ) - (189 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell188_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell188_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (47 / 200 : ℝ) - (189 / 3200 : ℝ)) ≤
      (1 / (250686381277 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (250686381277 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((189 / 3200 : ℝ) - Real.pi * Real.exp (47 / 200 : ℝ)) ≤
      (2 / (250686381277 / 5000000000 : ℝ) : ℝ) := by
    rw [show (189 / 3200 : ℝ) - Real.pi * Real.exp (47 / 200 : ℝ) =
      -(Real.pi * Real.exp (47 / 200 : ℝ) - (189 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (19893994626345931 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (19893994626345931 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell188_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (47 / 400 : ℝ) (189 / 1600 : ℝ)) :
    (7801582981 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15778465501 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell188_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell188_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell189_leftExp :
    (12664908933 / 10000000000 : ℝ) ≤ Real.exp (189 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (189 / 800 : ℝ) (251852533163 / 250000000000 : ℝ)
    (12664908933 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell189_rightExp :
    Real.exp (19 / 80 : ℝ) ≤ (792546873 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (19 / 80 : ℝ) (1007449485379 / 1000000000000 : ℝ)
    (792546873 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell189_denomUpper :
    Real.exp (2452945645888689 / 625000000000000 : ℝ) ≤ (101277088809 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (2452945645888689 / 625000000000000 : ℝ) (141310701041 /
    125000000000 : ℝ) (101277088809 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell189_denomLower :
    (251856774527 / 5000000000 : ℝ) ≤ Real.exp (4899278323080167 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4899278323080167 / 1250000000000000 : ℝ) (1130298727127
    / 1000000000000 : ℝ) (251856774527 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell189_product_lower :
    (4973497073080167 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (189 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell189_leftExp
    (by norm_num : (0 : ℝ) ≤ (12664908933 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell189_product_upper :
    Real.pi * Real.exp (19 / 80 : ℝ) ≤ (2489859708388689 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell189_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell189_endpointLower :
    (15581228781 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (189 / 1600 : ℝ) (19 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4973497073080167 / 1250000000000000 : ℝ) (Real.pi * Real.exp (189 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell189_product_lower
  have hD : Real.exp (Real.pi * Real.exp (19 / 80 : ℝ) - (189 / 3200 : ℝ)) ≤
      (101277088809 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell189_denomUpper
    linarith [hpThetaJensenCell189_product_upper]
  have hi : (1 / (101277088809 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (19 / 80 : ℝ) - (189 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (101277088809 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (101277088809 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((189 / 3200 : ℝ) - Real.pi * Real.exp (19 / 80 : ℝ)) := by
    rw [show (189 / 3200 : ℝ) - Real.pi * Real.exp (19 / 80 : ℝ) =
      -(Real.pi * Real.exp (19 / 80 : ℝ) - (189 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (189 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (189 / 800 : ℝ)) := by
    have h := hpThetaJensenCell189_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (101277088809 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell189_endpointUpper :
    hpThetaJensenKernelEndpointUpper (189 / 1600 : ℝ) (19 / 160 : ℝ) ≤ (1969544489 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (19 / 80 : ℝ)) (2489859708388689 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (19 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell189_product_upper
  have hD : (251856774527 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (189 / 800 : ℝ) - (19 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell189_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell189_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (189 / 800 : ℝ) - (19 / 320 : ℝ)) ≤
      (1 / (251856774527 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (251856774527 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((19 / 320 : ℝ) - Real.pi * Real.exp (189 / 800 : ℝ)) ≤
      (2 / (251856774527 / 5000000000 : ℝ) : ℝ) := by
    rw [show (19 / 320 : ℝ) - Real.pi * Real.exp (189 / 800 : ℝ) =
      -(Real.pi * Real.exp (189 / 800 : ℝ) - (19 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2489859708388689 / 625000000000000 : ℝ) ^ 2 - 6 *
      (2489859708388689 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell189_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (189 / 1600 : ℝ) (19 / 160 : ℝ)) :
    (15581228781 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1969544489 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell189_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell189_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell190_leftExp :
    (12680749967 / 10000000000 : ℝ) ≤ Real.exp (19 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (19 / 80 : ℝ) (503724742689 / 500000000000 : ℝ)
    (12680749967 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell190_rightExp :
    Real.exp (191 / 800 : ℝ) ≤ (12696610817 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (191 / 800 : ℝ) (251872209911 / 250000000000 : ℝ)
    (12696610817 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell190_denomUpper :
    Real.exp (39293833666411481 / 10000000000000000 : ℝ) ≤ (63594495507 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (39293833666411481 / 10000000000000000 : ℝ) (35332831637
    / 31250000000 : ℝ) (63594495507 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell190_denomLower :
    (101213682023 / 2000000000 : ℝ) ≤ Real.exp (4905108456290933 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4905108456290933 / 1250000000000000 : ℝ) (1130463483937
    / 1000000000000 : ℝ) (101213682023 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell190_product_lower :
    (4979717831290933 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (19 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell190_leftExp
    (by norm_num : (0 : ℝ) ≤ (12680749967 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell190_product_upper :
    Real.pi * Real.exp (191 / 800 : ℝ) ≤ (39887583666411481 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell190_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell190_endpointLower :
    (15559201969 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (19 / 160 : ℝ) (191 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4979717831290933 / 1250000000000000 : ℝ) (Real.pi * Real.exp (19 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell190_product_lower
  have hD : Real.exp (Real.pi * Real.exp (191 / 800 : ℝ) - (19 / 320 : ℝ)) ≤
      (63594495507 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell190_denomUpper
    linarith [hpThetaJensenCell190_product_upper]
  have hi : (1 / (63594495507 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (191 / 800 : ℝ) - (19 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (63594495507 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (63594495507 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((19 / 320 : ℝ) - Real.pi * Real.exp (191 / 800 : ℝ)) := by
    rw [show (19 / 320 : ℝ) - Real.pi * Real.exp (191 / 800 : ℝ) =
      -(Real.pi * Real.exp (191 / 800 : ℝ) - (19 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (19 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (19 / 80 : ℝ)) := by
    have h := hpThetaJensenCell190_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (63594495507 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell190_endpointUpper :
    hpThetaJensenKernelEndpointUpper (19 / 160 : ℝ) (191 / 1600 : ℝ) ≤ (7867077841 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (191 / 800 : ℝ)) (39887583666411481 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (191 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell190_product_upper
  have hD : (101213682023 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (19 / 80 : ℝ) - (191 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell190_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell190_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (19 / 80 : ℝ) - (191 / 3200 : ℝ)) ≤
      (1 / (101213682023 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (101213682023 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((191 / 3200 : ℝ) - Real.pi * Real.exp (19 / 80 : ℝ)) ≤
      (2 / (101213682023 / 2000000000 : ℝ) : ℝ) := by
    rw [show (191 / 3200 : ℝ) - Real.pi * Real.exp (19 / 80 : ℝ) =
      -(Real.pi * Real.exp (19 / 80 : ℝ) - (191 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (39887583666411481 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (39887583666411481 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell190_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (19 / 160 : ℝ) (191 / 1600 : ℝ)) :
    (15559201969 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7867077841 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell190_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell190_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell191_leftExp :
    (12399034 / 9765625 : ℝ) ≤ Real.exp (191 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (191 / 800 : ℝ) (1007488839643 / 1000000000000 : ℝ)
    (12399034 / 9765625 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell191_rightExp :
    Real.exp (6 / 25 : ℝ) ≤ (794530719 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (6 / 25 : ℝ) (201505639089 / 200000000000 : ℝ)
    (794530719 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell191_denomUpper :
    Real.exp (2458787457595367 / 625000000000000 : ℝ) ≤ (102228153331 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (2458787457595367 / 625000000000000 : ℝ) (1130815860761 /
    1000000000000 : ℝ) (102228153331 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell191_denomLower :
    (254218722603 / 5000000000 : ℝ) ≤ Real.exp (2397923032633 / 610351562500 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2397923032633 / 610351562500 : ℝ) (282657121177 /
    250000000000 : ℝ) (254218722603 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell191_product_lower :
    (2434544126383 / 610351562500 : ℝ) ≤ Real.pi * Real.exp (191 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell191_leftExp
    (by norm_num : (0 : ℝ) ≤ (12399034 / 9765625 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell191_product_upper :
    Real.pi * Real.exp (6 / 25 : ℝ) ≤ (2496092145095367 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell191_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell191_endpointLower :
    (15537085951 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (191 / 1600 : ℝ) (3 / 25 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2434544126383 / 610351562500 : ℝ) (Real.pi * Real.exp (191 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell191_product_lower
  have hD : Real.exp (Real.pi * Real.exp (6 / 25 : ℝ) - (191 / 3200 : ℝ)) ≤
      (102228153331 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell191_denomUpper
    linarith [hpThetaJensenCell191_product_upper]
  have hi : (1 / (102228153331 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (6 / 25 : ℝ) - (191 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (102228153331 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (102228153331 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((191 / 3200 : ℝ) - Real.pi * Real.exp (6 / 25 : ℝ)) := by
    rw [show (191 / 3200 : ℝ) - Real.pi * Real.exp (6 / 25 : ℝ) =
      -(Real.pi * Real.exp (6 / 25 : ℝ) - (191 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (191 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (191 / 800 : ℝ)) := by
    have h := hpThetaJensenCell191_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (102228153331 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell191_endpointUpper :
    hpThetaJensenKernelEndpointUpper (191 / 1600 : ℝ) (3 / 25 : ℝ) ≤ (15711865207 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (6 / 25 : ℝ)) (2496092145095367 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (3 / 25 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell191_product_upper
  have hD : (254218722603 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (191 / 800 : ℝ) - (3 / 50 : ℝ)) := by
    apply le_trans hpThetaJensenCell191_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell191_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (191 / 800 : ℝ) - (3 / 50 : ℝ)) ≤
      (1 / (254218722603 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (254218722603 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((3 / 50 : ℝ) - Real.pi * Real.exp (191 / 800 : ℝ)) ≤
      (2 / (254218722603 / 5000000000 : ℝ) : ℝ) := by
    rw [show (3 / 50 : ℝ) - Real.pi * Real.exp (191 / 800 : ℝ) =
      -(Real.pi * Real.exp (191 / 800 : ℝ) - (3 / 50 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2496092145095367 / 625000000000000 : ℝ) ^ 2 - 6 *
      (2496092145095367 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell191_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (191 / 1600 : ℝ) (3 / 25 : ℝ)) :
    (15537085951 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15711865207 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell191_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell191_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell192_leftExp :
    (6356245751 / 5000000000 : ℝ) ≤ Real.exp (6 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6 / 25 : ℝ) (251882048861 / 250000000000 : ℝ)
    (6356245751 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell192_rightExp :
    Real.exp (193 / 800 : ℝ) ≤ (6364196027 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (193 / 800 : ℝ) (62972972049 / 62500000000 : ℝ)
    (6364196027 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell192_denomUpper :
    Real.exp (19693713689051011 / 5000000000000000 : ℝ) ≤ (513539952597 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (19693713689051011 / 5000000000000000 : ℝ) (226196270767
    / 200000000000 : ℝ) (513539952597 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell192_denomLower :
    (3192629711 / 62500000 : ℝ) ≤ Real.exp (2458396037671949 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2458396037671949 / 625000000000000 : ℝ) (1130793729783 /
    1000000000000 : ℝ) (3192629711 / 62500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell192_product_lower :
    (2496091350171949 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (6 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell192_leftExp
    (by norm_num : (0 : ℝ) ≤ (6356245751 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell192_product_upper :
    Real.pi * Real.exp (193 / 800 : ℝ) ≤ (19993713689051011 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell192_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell192_endpointLower :
    (15514881133 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (3 / 25 : ℝ) (193 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2496091350171949 / 625000000000000 : ℝ) (Real.pi * Real.exp (6 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell192_product_lower
  have hD : Real.exp (Real.pi * Real.exp (193 / 800 : ℝ) - (3 / 50 : ℝ)) ≤
      (513539952597 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell192_denomUpper
    linarith [hpThetaJensenCell192_product_upper]
  have hi : (1 / (513539952597 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (193 / 800 : ℝ) - (3 / 50 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (513539952597 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (513539952597 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((3 / 50 : ℝ) - Real.pi * Real.exp (193 / 800 : ℝ)) := by
    rw [show (3 / 50 : ℝ) - Real.pi * Real.exp (193 / 800 : ℝ) =
      -(Real.pi * Real.exp (193 / 800 : ℝ) - (3 / 50 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (6 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (6 / 25 : ℝ)) := by
    have h := hpThetaJensenCell192_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (513539952597 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell192_endpointUpper :
    hpThetaJensenKernelEndpointUpper (3 / 25 : ℝ) (193 / 1600 : ℝ) ≤ (15689484919 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (193 / 800 : ℝ)) (19993713689051011 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (193 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell192_product_upper
  have hD : (3192629711 / 62500000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (6 / 25 : ℝ) - (193 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell192_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell192_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (6 / 25 : ℝ) - (193 / 3200 : ℝ)) ≤
      (1 / (3192629711 / 62500000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3192629711 / 62500000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((193 / 3200 : ℝ) - Real.pi * Real.exp (6 / 25 : ℝ)) ≤
      (2 / (3192629711 / 62500000 : ℝ) : ℝ) := by
    rw [show (193 / 3200 : ℝ) - Real.pi * Real.exp (6 / 25 : ℝ) =
      -(Real.pi * Real.exp (6 / 25 : ℝ) - (193 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (19993713689051011 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (19993713689051011 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell192_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (3 / 25 : ℝ) (193 / 1600 : ℝ)) :
    (15514881133 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15689484919 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell192_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell192_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell193_leftExp :
    (12728392053 / 10000000000 : ℝ) ≤ Real.exp (193 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (193 / 800 : ℝ) (1007567552783 / 1000000000000 : ℝ)
    (12728392053 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell193_rightExp :
    Real.exp (97 / 400 : ℝ) ≤ (3186078123 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (97 / 400 : ℝ) (50380345583 / 50000000000 : ℝ)
    (3186078123 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell193_denomUpper :
    Real.exp (9858579478669939 / 2500000000000000 : ℝ) ≤ (8061775367 / 156250000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9858579478669939 / 2500000000000000 : ℝ) (565573545993 /
    500000000000 : ℝ) (8061775367 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell193_denomLower :
    (128304609247 / 2500000000 : ℝ) ≤ Real.exp (4922645580821047 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4922645580821047 / 1250000000000000 : ℝ) (565479609787 /
    500000000000 : ℝ) (128304609247 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell193_product_lower :
    (4998426830821047 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (193 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell193_leftExp
    (by norm_num : (0 : ℝ) ≤ (12728392053 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell193_product_upper :
    Real.pi * Real.exp (97 / 400 : ℝ) ≤ (10009360728669939 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell193_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell193_endpointLower :
    (15492587937 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (193 / 1600 : ℝ) (97 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4998426830821047 / 1250000000000000 : ℝ) (Real.pi * Real.exp (193 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell193_product_lower
  have hD : Real.exp (Real.pi * Real.exp (97 / 400 : ℝ) - (193 / 3200 : ℝ)) ≤
      (8061775367 / 156250000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell193_denomUpper
    linarith [hpThetaJensenCell193_product_upper]
  have hi : (1 / (8061775367 / 156250000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (97 / 400 : ℝ) - (193 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (8061775367 / 156250000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (8061775367 / 156250000 : ℝ) : ℝ) ≤
      2 * Real.exp ((193 / 3200 : ℝ) - Real.pi * Real.exp (97 / 400 : ℝ)) := by
    rw [show (193 / 3200 : ℝ) - Real.pi * Real.exp (97 / 400 : ℝ) =
      -(Real.pi * Real.exp (97 / 400 : ℝ) - (193 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (193 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (193 / 800 : ℝ)) := by
    have h := hpThetaJensenCell193_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (8061775367 / 156250000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell193_endpointUpper :
    hpThetaJensenKernelEndpointUpper (193 / 1600 : ℝ) (97 / 800 : ℝ) ≤ (979188451 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (97 / 400 : ℝ)) (10009360728669939 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (97 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell193_product_upper
  have hD : (128304609247 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (193 / 800 : ℝ) - (97 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell193_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell193_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (193 / 800 : ℝ) - (97 / 1600 : ℝ)) ≤
      (1 / (128304609247 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (128304609247 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((97 / 1600 : ℝ) - Real.pi * Real.exp (193 / 800 : ℝ)) ≤
      (2 / (128304609247 / 2500000000 : ℝ) : ℝ) := by
    rw [show (97 / 1600 : ℝ) - Real.pi * Real.exp (193 / 800 : ℝ) =
      -(Real.pi * Real.exp (193 / 800 : ℝ) - (97 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (10009360728669939 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (10009360728669939 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell193_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (193 / 1600 : ℝ) (97 / 800 : ℝ)) :
    (15492587937 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (979188451 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell193_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell193_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell194_leftExp :
    (12744312491 / 10000000000 : ℝ) ≤ Real.exp (97 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (97 / 400 : ℝ) (1007606911659 / 1000000000000 : ℝ)
    (12744312491 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell194_rightExp :
    Real.exp (39 / 160 : ℝ) ≤ (3190063211 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (39 / 160 : ℝ) (503823136037 / 500000000000 : ℝ)
    (3190063211 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell194_denomUpper :
    Real.exp (9870317753235123 / 2500000000000000 : ℝ) ≤ (103676376371 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9870317753235123 / 2500000000000000 : ℝ) (565656537801 /
    500000000000 : ℝ) (103676376371 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell194_denomLower :
    (515630595913 / 10000000000 : ℝ) ≤ Real.exp (4928506895903209 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4928506895903209 / 1250000000000000 : ℝ) (45244998177 /
    40000000000 : ℝ) (515630595913 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell194_product_lower :
    (5004678770903209 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (97 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell194_leftExp
    (by norm_num : (0 : ℝ) ≤ (12744312491 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell194_product_upper :
    Real.pi * Real.exp (39 / 160 : ℝ) ≤ (10021880253235123 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell194_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell194_endpointLower :
    (3867551691 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (97 / 800 : ℝ) (39 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5004678770903209 / 1250000000000000 : ℝ) (Real.pi * Real.exp (97 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell194_product_lower
  have hD : Real.exp (Real.pi * Real.exp (39 / 160 : ℝ) - (97 / 1600 : ℝ)) ≤
      (103676376371 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell194_denomUpper
    linarith [hpThetaJensenCell194_product_upper]
  have hi : (1 / (103676376371 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (39 / 160 : ℝ) - (97 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (103676376371 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (103676376371 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((97 / 1600 : ℝ) - Real.pi * Real.exp (39 / 160 : ℝ)) := by
    rw [show (97 / 1600 : ℝ) - Real.pi * Real.exp (39 / 160 : ℝ) =
      -(Real.pi * Real.exp (39 / 160 : ℝ) - (97 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (97 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (97 / 400 : ℝ)) := by
    have h := hpThetaJensenCell194_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (103676376371 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell194_endpointUpper :
    hpThetaJensenKernelEndpointUpper (97 / 800 : ℝ) (39 / 320 : ℝ) ≤ (15644456537 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (39 / 160 : ℝ)) (10021880253235123 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (39 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell194_product_upper
  have hD : (515630595913 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (97 / 400 : ℝ) - (39 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell194_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell194_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (97 / 400 : ℝ) - (39 / 640 : ℝ)) ≤
      (1 / (515630595913 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (515630595913 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((39 / 640 : ℝ) - Real.pi * Real.exp (97 / 400 : ℝ)) ≤
      (2 / (515630595913 / 10000000000 : ℝ) : ℝ) := by
    rw [show (39 / 640 : ℝ) - Real.pi * Real.exp (97 / 400 : ℝ) =
      -(Real.pi * Real.exp (97 / 400 : ℝ) - (39 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (10021880253235123 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (10021880253235123 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell194_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (97 / 800 : ℝ) (39 / 320 : ℝ)) :
    (3867551691 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15644456537 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell194_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell194_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell195_leftExp :
    (6380126421 / 5000000000 : ℝ) ≤ Real.exp (39 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (39 / 160 : ℝ) (1007646272073 / 1000000000000 : ℝ)
    (6380126421 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell195_rightExp :
    Real.exp (49 / 200 : ℝ) ≤ (12776213133 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (49 / 200 : ℝ) (40307425361 / 40000000000 : ℝ)
    (12776213133 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell195_denomUpper :
    Real.exp (39528286745140869 / 10000000000000000 : ℝ) ≤ (260412415289 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (39528286745140869 / 10000000000000000 : ℝ) (14143491313
    / 12500000000 : ℝ) (260412415289 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell195_denomLower :
    (518057333009 / 10000000000 : ℝ) ≤ Real.exp (2467188015400279 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2467188015400279 / 625000000000000 : ℝ) (45251637389 /
    40000000000 : ℝ) (518057333009 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell195_product_lower :
    (2505469265400279 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (39 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell195_leftExp
    (by norm_num : (0 : ℝ) ≤ (6380126421 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell195_product_upper :
    Real.pi * Real.exp (49 / 200 : ℝ) ≤ (40137661745140869 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell195_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell195_endpointLower :
    (3861934511 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (39 / 320 : ℝ) (49 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2505469265400279 / 625000000000000 : ℝ) (Real.pi * Real.exp (39 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell195_product_lower
  have hD : Real.exp (Real.pi * Real.exp (49 / 200 : ℝ) - (39 / 640 : ℝ)) ≤
      (260412415289 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell195_denomUpper
    linarith [hpThetaJensenCell195_product_upper]
  have hi : (1 / (260412415289 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (49 / 200 : ℝ) - (39 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (260412415289 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (260412415289 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((39 / 640 : ℝ) - Real.pi * Real.exp (49 / 200 : ℝ)) := by
    rw [show (39 / 640 : ℝ) - Real.pi * Real.exp (49 / 200 : ℝ) =
      -(Real.pi * Real.exp (49 / 200 : ℝ) - (39 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (39 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (39 / 160 : ℝ)) := by
    have h := hpThetaJensenCell195_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (260412415289 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell195_endpointUpper :
    hpThetaJensenKernelEndpointUpper (39 / 320 : ℝ) (49 / 400 : ℝ) ≤ (1952726161 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (49 / 200 : ℝ)) (40137661745140869 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (49 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell195_product_upper
  have hD : (518057333009 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (39 / 160 : ℝ) - (49 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell195_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell195_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (39 / 160 : ℝ) - (49 / 800 : ℝ)) ≤
      (1 / (518057333009 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (518057333009 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((49 / 800 : ℝ) - Real.pi * Real.exp (39 / 160 : ℝ)) ≤
      (2 / (518057333009 / 10000000000 : ℝ) : ℝ) := by
    rw [show (49 / 800 : ℝ) - Real.pi * Real.exp (39 / 160 : ℝ) =
      -(Real.pi * Real.exp (39 / 160 : ℝ) - (49 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (40137661745140869 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (40137661745140869 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell195_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (39 / 320 : ℝ) (49 / 400 : ℝ)) :
    (3861934511 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1952726161 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell195_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell195_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell196_leftExp :
    (12776213131 / 10000000000 : ℝ) ≤ Real.exp (49 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (49 / 200 : ℝ) (125960704253 / 125000000000 : ℝ)
    (12776213131 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell196_rightExp :
    Real.exp (197 / 800 : ℝ) ≤ (2558438677 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (197 / 800 : ℝ) (503862498757 / 500000000000 : ℝ)
    (2558438677 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell196_denomUpper :
    Real.exp (7915073038592461 / 2000000000000000 : ℝ) ≤ (104656514767 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7915073038592461 / 2000000000000000 : ℝ) (113164578069 /
    100000000000 : ℝ) (104656514767 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell196_denomLower :
    (260249375707 / 5000000000 : ℝ) ≤ Real.exp (4940252995330569 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4940252995330569 / 1250000000000000 : ℝ) (1131457160853
    / 1000000000000 : ℝ) (260249375707 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell196_product_lower :
    (5017206120330569 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (49 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell196_leftExp
    (by norm_num : (0 : ℝ) ≤ (12776213131 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell196_product_upper :
    Real.pi * Real.exp (197 / 800 : ℝ) ≤ (8037573038592461 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell196_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell196_endpointLower :
    (1542518219 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (49 / 400 : ℝ) (197 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5017206120330569 / 1250000000000000 : ℝ) (Real.pi * Real.exp (49 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell196_product_lower
  have hD : Real.exp (Real.pi * Real.exp (197 / 800 : ℝ) - (49 / 800 : ℝ)) ≤
      (104656514767 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell196_denomUpper
    linarith [hpThetaJensenCell196_product_upper]
  have hi : (1 / (104656514767 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (197 / 800 : ℝ) - (49 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (104656514767 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (104656514767 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((49 / 800 : ℝ) - Real.pi * Real.exp (197 / 800 : ℝ)) := by
    rw [show (49 / 800 : ℝ) - Real.pi * Real.exp (197 / 800 : ℝ) =
      -(Real.pi * Real.exp (197 / 800 : ℝ) - (49 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (49 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (49 / 200 : ℝ)) := by
    have h := hpThetaJensenCell196_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (104656514767 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell196_endpointUpper :
    hpThetaJensenKernelEndpointUpper (49 / 400 : ℝ) (197 / 1600 : ℝ) ≤ (15599073893 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (197 / 800 : ℝ)) (8037573038592461 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (197 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell196_product_upper
  have hD : (260249375707 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (49 / 200 : ℝ) - (197 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell196_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell196_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (49 / 200 : ℝ) - (197 / 3200 : ℝ)) ≤
      (1 / (260249375707 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (260249375707 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((197 / 3200 : ℝ) - Real.pi * Real.exp (49 / 200 : ℝ)) ≤
      (2 / (260249375707 / 5000000000 : ℝ) : ℝ) := by
    rw [show (197 / 3200 : ℝ) - Real.pi * Real.exp (49 / 200 : ℝ) =
      -(Real.pi * Real.exp (49 / 200 : ℝ) - (197 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8037573038592461 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (8037573038592461 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell196_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (49 / 400 : ℝ) (197 / 1600 : ℝ)) :
    (1542518219 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15599073893 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell196_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell196_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell197_leftExp :
    (12792193383 / 10000000000 : ℝ) ≤ Real.exp (197 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (197 / 800 : ℝ) (1007724997513 / 1000000000000 : ℝ)
    (12792193383 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell197_rightExp :
    Real.exp (99 / 400 : ℝ) ≤ (102465549 / 80000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (99 / 400 : ℝ) (1007764362541 / 1000000000000 : ℝ)
    (102465549 / 80000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell197_denomUpper :
    Real.exp (316980051479557 / 80000000000000 : ℝ) ≤ (525755216481 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (316980051479557 / 80000000000000 : ℝ) (282953125733 /
    250000000000 : ℝ) (525755216481 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell197_denomLower :
    (104590991019 / 2000000000 : ℝ) ≤ Real.exp (4946137799310717 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4946137799310717 / 1250000000000000 : ℝ) (1131623633189
    / 1000000000000 : ℝ) (104590991019 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell197_product_lower :
    (5023481549310717 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (197 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell197_leftExp
    (by norm_num : (0 : ℝ) ≤ (12792193383 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell197_product_upper :
    Real.pi * Real.exp (99 / 400 : ℝ) ≤ (321905051479557 / 80000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell197_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell197_endpointLower :
    (15402539621 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (197 / 1600 : ℝ) (99 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5023481549310717 / 1250000000000000 : ℝ) (Real.pi * Real.exp (197 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell197_product_lower
  have hD : Real.exp (Real.pi * Real.exp (99 / 400 : ℝ) - (197 / 3200 : ℝ)) ≤
      (525755216481 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell197_denomUpper
    linarith [hpThetaJensenCell197_product_upper]
  have hi : (1 / (525755216481 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (99 / 400 : ℝ) - (197 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (525755216481 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (525755216481 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((197 / 3200 : ℝ) - Real.pi * Real.exp (99 / 400 : ℝ)) := by
    rw [show (197 / 3200 : ℝ) - Real.pi * Real.exp (99 / 400 : ℝ) =
      -(Real.pi * Real.exp (99 / 400 : ℝ) - (197 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (197 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (197 / 800 : ℝ)) := by
    have h := hpThetaJensenCell197_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (525755216481 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell197_endpointUpper :
    hpThetaJensenKernelEndpointUpper (197 / 1600 : ℝ) (99 / 800 : ℝ) ≤ (7788125387 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (99 / 400 : ℝ)) (321905051479557 / 80000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (99 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell197_product_upper
  have hD : (104590991019 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (197 / 800 : ℝ) - (99 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell197_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell197_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (197 / 800 : ℝ) - (99 / 1600 : ℝ)) ≤
      (1 / (104590991019 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (104590991019 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((99 / 1600 : ℝ) - Real.pi * Real.exp (197 / 800 : ℝ)) ≤
      (2 / (104590991019 / 2000000000 : ℝ) : ℝ) := by
    rw [show (99 / 1600 : ℝ) - Real.pi * Real.exp (197 / 800 : ℝ) =
      -(Real.pi * Real.exp (197 / 800 : ℝ) - (99 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (321905051479557 / 80000000000000 : ℝ) ^ 2 - 6 *
      (321905051479557 / 80000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell197_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (197 / 1600 : ℝ) (99 / 800 : ℝ)) :
    (15402539621 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7788125387 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell197_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell197_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell198_leftExp :
    (12808193623 / 10000000000 : ℝ) ≤ Real.exp (99 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (99 / 400 : ℝ) (50388218127 / 50000000000 : ℝ)
    (12808193623 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell198_rightExp :
    Real.exp (199 / 800 : ℝ) ≤ (12824213877 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (199 / 800 : ℝ) (201560745821 / 200000000000 : ℝ)
    (12824213877 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell198_denomUpper :
    Real.exp (39669710546486061 / 10000000000000000 : ℝ) ≤ (66030358001 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (39669710546486061 / 10000000000000000 : ℝ)
    (1131979472133 / 1000000000000 : ℝ) (66030358001 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell198_denomLower :
    (131356512203 / 2500000000 : ℝ) ≤ Real.exp (4952030452558477 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4952030452558477 / 1250000000000000 : ℝ) (1131790352111
    / 1000000000000 : ℝ) (131356512203 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell198_product_lower :
    (5029764827558477 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (99 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell198_leftExp
    (by norm_num : (0 : ℝ) ≤ (12808193623 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell198_product_upper :
    Real.pi * Real.exp (199 / 800 : ℝ) ≤ (40288460546486061 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell198_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell198_endpointLower :
    (3075962153 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (99 / 800 : ℝ) (199 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5029764827558477 / 1250000000000000 : ℝ) (Real.pi * Real.exp (99 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell198_product_lower
  have hD : Real.exp (Real.pi * Real.exp (199 / 800 : ℝ) - (99 / 1600 : ℝ)) ≤
      (66030358001 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell198_denomUpper
    linarith [hpThetaJensenCell198_product_upper]
  have hi : (1 / (66030358001 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (199 / 800 : ℝ) - (99 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (66030358001 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (66030358001 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((99 / 1600 : ℝ) - Real.pi * Real.exp (199 / 800 : ℝ)) := by
    rw [show (99 / 1600 : ℝ) - Real.pi * Real.exp (199 / 800 : ℝ) =
      -(Real.pi * Real.exp (199 / 800 : ℝ) - (99 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (99 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (99 / 400 : ℝ)) := by
    have h := hpThetaJensenCell198_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (66030358001 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell198_endpointUpper :
    hpThetaJensenKernelEndpointUpper (99 / 800 : ℝ) (199 / 1600 : ℝ) ≤ (311066807 / 200000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (199 / 800 : ℝ)) (40288460546486061 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (199 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell198_product_upper
  have hD : (131356512203 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (99 / 400 : ℝ) - (199 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell198_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell198_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (99 / 400 : ℝ) - (199 / 3200 : ℝ)) ≤
      (1 / (131356512203 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (131356512203 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((199 / 3200 : ℝ) - Real.pi * Real.exp (99 / 400 : ℝ)) ≤
      (2 / (131356512203 / 2500000000 : ℝ) : ℝ) := by
    rw [show (199 / 3200 : ℝ) - Real.pi * Real.exp (99 / 400 : ℝ) =
      -(Real.pi * Real.exp (99 / 400 : ℝ) - (199 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (40288460546486061 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (40288460546486061 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell198_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (99 / 800 : ℝ) (199 / 1600 : ℝ)) :
    (3075962153 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (311066807 / 200000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell198_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell198_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell199_leftExp :
    (3206053469 / 2500000000 : ℝ) ≤ Real.exp (199 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (199 / 800 : ℝ) (62987733069 / 62500000000 : ℝ)
    (3206053469 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell199_rightExp :
    Real.exp (1 / 4 : ℝ) ≤ (1605031771 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1 / 4 : ℝ) (1007843097207 / 1000000000000 : ℝ)
    (1605031771 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell199_denomUpper :
    Real.exp (4964622201551203 / 1250000000000000 : ℝ) ≤ (530745623281 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4964622201551203 / 1250000000000000 : ℝ) (141518336087 /
    125000000000 : ℝ) (530745623281 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell199_denomLower :
    (65989017273 / 1250000000 : ℝ) ≤ Real.exp (1239482741222831 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1239482741222831 / 312500000000000 : ℝ) (1131957317999 /
    1000000000000 : ℝ) (65989017273 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell199_product_lower :
    (1259013991222831 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (199 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell199_leftExp
    (by norm_num : (0 : ℝ) ≤ (3206053469 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell199_product_upper :
    Real.pi * Real.exp (1 / 4 : ℝ) ≤ (5042356576551203 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell199_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell199_endpointLower :
    (15356996031 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (199 / 1600 : ℝ) (1 / 8 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1259013991222831 / 312500000000000 : ℝ) (Real.pi * Real.exp (199 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell199_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1 / 4 : ℝ) - (199 / 3200 : ℝ)) ≤
      (530745623281 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell199_denomUpper
    linarith [hpThetaJensenCell199_product_upper]
  have hi : (1 / (530745623281 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1 / 4 : ℝ) - (199 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (530745623281 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (530745623281 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((199 / 3200 : ℝ) - Real.pi * Real.exp (1 / 4 : ℝ)) := by
    rw [show (199 / 3200 : ℝ) - Real.pi * Real.exp (1 / 4 : ℝ) =
      -(Real.pi * Real.exp (1 / 4 : ℝ) - (199 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (199 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (199 / 800 : ℝ)) := by
    have h := hpThetaJensenCell199_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (530745623281 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell199_endpointUpper :
    hpThetaJensenKernelEndpointUpper (199 / 1600 : ℝ) (1 / 8 : ℝ) ≤ (15530343053 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1 / 4 : ℝ)) (5042356576551203 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1 / 8 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell199_product_upper
  have hD : (65989017273 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (199 / 800 : ℝ) - (1 / 16 : ℝ)) := by
    apply le_trans hpThetaJensenCell199_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell199_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (199 / 800 : ℝ) - (1 / 16 : ℝ)) ≤
      (1 / (65989017273 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (65989017273 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1 / 16 : ℝ) - Real.pi * Real.exp (199 / 800 : ℝ)) ≤
      (2 / (65989017273 / 1250000000 : ℝ) : ℝ) := by
    rw [show (1 / 16 : ℝ) - Real.pi * Real.exp (199 / 800 : ℝ) =
      -(Real.pi * Real.exp (199 / 800 : ℝ) - (1 / 16 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (5042356576551203 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (5042356576551203 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell199_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (199 / 1600 : ℝ) (1 / 8 : ℝ)) :
    (15356996031 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15530343053 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell199_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell199_endpointUpper

def hpThetaJensenCellsBatch009Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3155077617 / 2000000000 : ℝ)
  | 1 => (3150836507 / 2000000000 : ℝ)
  | 2 => (3933221029 / 2500000000 : ℝ)
  | 3 => (3927873309 / 2500000000 : ℝ)
  | 4 => (15690010293 / 10000000000 : ℝ)
  | 5 => (1958554461 / 1250000000 : ℝ)
  | 6 => (15646769827 / 10000000000 : ℝ)
  | 7 => (7812506557 / 5000000000 : ℝ)
  | 8 => (7801582981 / 5000000000 : ℝ)
  | 9 => (15581228781 / 10000000000 : ℝ)
  | 10 => (15559201969 / 10000000000 : ℝ)
  | 11 => (15537085951 / 10000000000 : ℝ)
  | 12 => (15514881133 / 10000000000 : ℝ)
  | 13 => (15492587937 / 10000000000 : ℝ)
  | 14 => (3867551691 / 2500000000 : ℝ)
  | 15 => (3861934511 / 2500000000 : ℝ)
  | 16 => (1542518219 / 1000000000 : ℝ)
  | 17 => (15402539621 / 10000000000 : ℝ)
  | 18 => (3075962153 / 2000000000 : ℝ)
  | 19 => (15356996031 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch009Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1994003693 / 1250000000 : ℝ)
  | 1 => (15930659901 / 10000000000 : ℝ)
  | 2 => (15909196347 / 10000000000 : ℝ)
  | 3 => (7943819641 / 5000000000 : ℝ)
  | 4 => (15865989107 / 10000000000 : ℝ)
  | 5 => (3168849247 / 2000000000 : ℝ)
  | 6 => (247225173 / 156250000 : ℝ)
  | 7 => (632019361 / 400000000 : ℝ)
  | 8 => (15778465501 / 10000000000 : ℝ)
  | 9 => (1969544489 / 1250000000 : ℝ)
  | 10 => (7867077841 / 5000000000 : ℝ)
  | 11 => (15711865207 / 10000000000 : ℝ)
  | 12 => (15689484919 / 10000000000 : ℝ)
  | 13 => (979188451 / 625000000 : ℝ)
  | 14 => (15644456537 / 10000000000 : ℝ)
  | 15 => (1952726161 / 1250000000 : ℝ)
  | 16 => (15599073893 / 10000000000 : ℝ)
  | 17 => (7788125387 / 5000000000 : ℝ)
  | 18 => (311066807 / 200000000 : ℝ)
  | 19 => (15530343053 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch009_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((180 : ℝ) + (j.val : ℝ)) / 1600)
      (((180 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch009Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch009Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell180_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell181_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell182_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell183_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell184_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell185_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell186_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell187_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell188_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell189_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell190_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell191_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell192_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell193_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell194_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell195_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell196_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell197_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell198_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell199_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper] at h ⊢
    exact h

end HodgeProofHP
