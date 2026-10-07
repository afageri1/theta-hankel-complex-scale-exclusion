import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell820_leftExp :
    (5574190921 / 2000000000 : ℝ) ≤ Real.exp (41 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (41 / 40 : ℝ) (1032549771981 / 1000000000000 : ℝ)
    (5574190921 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell820_rightExp :
    Real.exp (821 / 800 : ℝ) ≤ (27905815083 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (821 / 800 : ℝ) (206518021349 / 200000000000 : ℝ)
    (27905815083 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell820_denomUpper :
    Real.exp (85106213324047219 / 10000000000000000 : ℝ) ≤ (49672484421887 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (85106213324047219 / 10000000000000000 : ℝ) (52187153901
    / 40000000000 : ℝ) (49672484421887 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell820_denomLower :
    (49115964079291 / 10000000000 : ℝ) ≤ Real.exp (2124838575485779 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2124838575485779 / 250000000000000 : ℝ) (326054889469 /
    250000000000 : ℝ) (49115964079291 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell820_product_lower :
    (2188979200485779 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (41 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell820_leftExp
    (by norm_num : (0 : ℝ) ≤ (5574190921 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell820_product_upper :
    Real.pi * Real.exp (821 / 800 : ℝ) ≤ (87668713324047219 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell820_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell820_endpointLower :
    (204643531 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (41 / 80 : ℝ) (821 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2188979200485779 / 250000000000000 : ℝ) (Real.pi * Real.exp (41 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell820_product_lower
  have hD : Real.exp (Real.pi * Real.exp (821 / 800 : ℝ) - (41 / 160 : ℝ)) ≤
      (49672484421887 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell820_denomUpper
    linarith [hpThetaJensenCell820_product_upper]
  have hi : (1 / (49672484421887 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (821 / 800 : ℝ) - (41 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (49672484421887 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (49672484421887 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((41 / 160 : ℝ) - Real.pi * Real.exp (821 / 800 : ℝ)) := by
    rw [show (41 / 160 : ℝ) - Real.pi * Real.exp (821 / 800 : ℝ) =
      -(Real.pi * Real.exp (821 / 800 : ℝ) - (41 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (41 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (41 / 40 : ℝ)) := by
    have h := hpThetaJensenCell820_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (49672484421887 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell820_endpointUpper :
    hpThetaJensenKernelEndpointUpper (41 / 80 : ℝ) (821 / 1600 : ℝ) ≤ (260100777 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (821 / 800 : ℝ)) (87668713324047219 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (821 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell820_product_upper
  have hD : (49115964079291 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (41 / 40 : ℝ) - (821 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell820_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell820_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (41 / 40 : ℝ) - (821 / 3200 : ℝ)) ≤
      (1 / (49115964079291 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (49115964079291 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((821 / 3200 : ℝ) - Real.pi * Real.exp (41 / 40 : ℝ)) ≤
      (2 / (49115964079291 / 10000000000 : ℝ) : ℝ) := by
    rw [show (821 / 3200 : ℝ) - Real.pi * Real.exp (41 / 40 : ℝ) =
      -(Real.pi * Real.exp (41 / 40 : ℝ) - (821 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (87668713324047219 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (87668713324047219 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell820_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (41 / 80 : ℝ) (821 / 1600 : ℝ)) :
    (204643531 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (260100777 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell820_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell820_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell821_leftExp :
    (27905815081 / 10000000000 : ℝ) ≤ Real.exp (821 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (821 / 800 : ℝ) (129073763343 / 125000000000 : ℝ)
    (27905815081 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell821_rightExp :
    Real.exp (411 / 400 : ℝ) ≤ (27940719163 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (411 / 400 : ℝ) (258157610771 / 250000000000 : ℝ)
    (27940719163 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell821_denomUpper :
    Real.exp (85212742737446659 / 10000000000000000 : ℝ) ≤ (50204471065209 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (85212742737446659 / 10000000000000000 : ℝ) (65255662659
    / 50000000000 : ℝ) (50204471065209 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell821_denomLower :
    (9928262051529 / 2000000000 : ℝ) ≤ Real.exp (10637491926493619 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10637491926493619 / 1250000000000000 : ℝ) (260930650393
    / 200000000000 : ℝ) (9928262051529 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell821_product_lower :
    (10958585676493619 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (821 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell821_leftExp
    (by norm_num : (0 : ℝ) ≤ (27905815081 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell821_product_upper :
    Real.pi * Real.exp (411 / 400 : ℝ) ≤ (87778367737446659 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell821_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell821_endpointLower :
    (203034287 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (821 / 1600 : ℝ) (411 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10958585676493619 / 1250000000000000 : ℝ) (Real.pi * Real.exp (821 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell821_product_lower
  have hD : Real.exp (Real.pi * Real.exp (411 / 400 : ℝ) - (821 / 3200 : ℝ)) ≤
      (50204471065209 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell821_denomUpper
    linarith [hpThetaJensenCell821_product_upper]
  have hi : (1 / (50204471065209 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (411 / 400 : ℝ) - (821 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (50204471065209 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (50204471065209 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((821 / 3200 : ℝ) - Real.pi * Real.exp (411 / 400 : ℝ)) := by
    rw [show (821 / 3200 : ℝ) - Real.pi * Real.exp (411 / 400 : ℝ) =
      -(Real.pi * Real.exp (411 / 400 : ℝ) - (821 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (821 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (821 / 800 : ℝ)) := by
    have h := hpThetaJensenCell821_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (50204471065209 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell821_endpointUpper :
    hpThetaJensenKernelEndpointUpper (821 / 1600 : ℝ) (411 / 800 : ℝ) ≤ (1032235489 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (411 / 400 : ℝ)) (87778367737446659 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (411 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell821_product_upper
  have hD : (9928262051529 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (821 / 800 : ℝ) - (411 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell821_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell821_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (821 / 800 : ℝ) - (411 / 1600 : ℝ)) ≤
      (1 / (9928262051529 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (9928262051529 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((411 / 1600 : ℝ) - Real.pi * Real.exp (821 / 800 : ℝ)) ≤
      (2 / (9928262051529 / 2000000000 : ℝ) : ℝ) := by
    rw [show (411 / 1600 : ℝ) - Real.pi * Real.exp (821 / 800 : ℝ) =
      -(Real.pi * Real.exp (821 / 800 : ℝ) - (411 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (87778367737446659 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (87778367737446659 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell821_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (821 / 1600 : ℝ) (411 / 800 : ℝ)) :
    (203034287 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1032235489 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell821_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell821_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell822_leftExp :
    (27940719161 / 10000000000 : ℝ) ≤ Real.exp (411 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (411 / 400 : ℝ) (1032630443083 / 1000000000000 : ℝ)
    (27940719161 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell822_rightExp :
    Real.exp (823 / 800 : ℝ) ≤ (27975666899 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (823 / 800 : ℝ) (516335390499 / 500000000000 : ℝ)
    (27975666899 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell822_denomUpper :
    Real.exp (85319409300230107 / 10000000000000000 : ℝ) ≤ (25371425577017 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (85319409300230107 / 10000000000000000 : ℝ)
    (1305548363021 / 1000000000000 : ℝ) (25371425577017 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell822_denomLower :
    (1567905089177 / 312500000 : ℝ) ≤ Real.exp (10650808098805539 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10650808098805539 / 1250000000000000 : ℝ) (261017529791
    / 200000000000 : ℝ) (1567905089177 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell822_product_lower :
    (10972292473805539 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (411 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell822_leftExp
    (by norm_num : (0 : ℝ) ≤ (27940719161 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell822_product_upper :
    Real.pi * Real.exp (823 / 800 : ℝ) ≤ (87888159300230107 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell822_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell822_endpointLower :
    (503587141 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (411 / 800 : ℝ) (823 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10972292473805539 / 1250000000000000 : ℝ) (Real.pi * Real.exp (411 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell822_product_lower
  have hD : Real.exp (Real.pi * Real.exp (823 / 800 : ℝ) - (411 / 1600 : ℝ)) ≤
      (25371425577017 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell822_denomUpper
    linarith [hpThetaJensenCell822_product_upper]
  have hi : (1 / (25371425577017 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (823 / 800 : ℝ) - (411 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (25371425577017 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (25371425577017 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((411 / 1600 : ℝ) - Real.pi * Real.exp (823 / 800 : ℝ)) := by
    rw [show (411 / 1600 : ℝ) - Real.pi * Real.exp (823 / 800 : ℝ) =
      -(Real.pi * Real.exp (823 / 800 : ℝ) - (411 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (411 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (411 / 400 : ℝ)) := by
    have h := hpThetaJensenCell822_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (25371425577017 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell822_endpointUpper :
    hpThetaJensenKernelEndpointUpper (411 / 800 : ℝ) (823 / 1600 : ℝ) ≤ (1024117563 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (823 / 800 : ℝ)) (87888159300230107 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (823 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell822_product_upper
  have hD : (1567905089177 / 312500000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (411 / 400 : ℝ) - (823 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell822_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell822_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (411 / 400 : ℝ) - (823 / 3200 : ℝ)) ≤
      (1 / (1567905089177 / 312500000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1567905089177 / 312500000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((823 / 3200 : ℝ) - Real.pi * Real.exp (411 / 400 : ℝ)) ≤
      (2 / (1567905089177 / 312500000 : ℝ) : ℝ) := by
    rw [show (823 / 3200 : ℝ) - Real.pi * Real.exp (411 / 400 : ℝ) =
      -(Real.pi * Real.exp (411 / 400 : ℝ) - (823 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (87888159300230107 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (87888159300230107 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell822_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (411 / 800 : ℝ) (823 / 1600 : ℝ)) :
    (503587141 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1024117563 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell822_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell822_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell823_leftExp :
    (27975666897 / 10000000000 : ℝ) ≤ Real.exp (823 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (823 / 800 : ℝ) (1032670780997 / 1000000000000 : ℝ)
    (27975666897 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell823_rightExp :
    Real.exp (103 / 100 : ℝ) ≤ (7002664587 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (103 / 100 : ℝ) (1032711120489 / 1000000000000 : ℝ)
    (7002664587 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell823_denomUpper :
    Real.exp (21356553297867091 / 2500000000000000 : ℝ) ≤ (12821927254291 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21356553297867091 / 2500000000000000 : ℝ) (326496044597
    / 250000000000 : ℝ) (12821927254291 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell823_denomLower :
    (25355502440031 / 5000000000 : ℝ) ≤ Real.exp (10664141414785003 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10664141414785003 / 1250000000000000 : ℝ) (652761375059
    / 500000000000 : ℝ) (25355502440031 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell823_product_lower :
    (10986016414785003 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (823 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell823_leftExp
    (by norm_num : (0 : ℝ) ≤ (27975666897 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell823_product_upper :
    Real.pi * Real.exp (103 / 100 : ℝ) ≤ (21999522047867091 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell823_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell823_endpointLower :
    (499613009 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (823 / 1600 : ℝ) (103 / 200 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10986016414785003 / 1250000000000000 : ℝ) (Real.pi * Real.exp (823 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell823_product_lower
  have hD : Real.exp (Real.pi * Real.exp (103 / 100 : ℝ) - (823 / 3200 : ℝ)) ≤
      (12821927254291 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell823_denomUpper
    linarith [hpThetaJensenCell823_product_upper]
  have hi : (1 / (12821927254291 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (103 / 100 : ℝ) - (823 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (12821927254291 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (12821927254291 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((823 / 3200 : ℝ) - Real.pi * Real.exp (103 / 100 : ℝ)) := by
    rw [show (823 / 3200 : ℝ) - Real.pi * Real.exp (103 / 100 : ℝ) =
      -(Real.pi * Real.exp (103 / 100 : ℝ) - (823 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (823 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (823 / 800 : ℝ)) := by
    have h := hpThetaJensenCell823_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (12821927254291 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell823_endpointUpper :
    hpThetaJensenKernelEndpointUpper (823 / 1600 : ℝ) (103 / 200 : ℝ) ≤ (1016049151 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (103 / 100 : ℝ)) (21999522047867091 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (103 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell823_product_upper
  have hD : (25355502440031 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (823 / 800 : ℝ) - (103 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell823_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell823_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (823 / 800 : ℝ) - (103 / 400 : ℝ)) ≤
      (1 / (25355502440031 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (25355502440031 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((103 / 400 : ℝ) - Real.pi * Real.exp (823 / 800 : ℝ)) ≤
      (2 / (25355502440031 / 5000000000 : ℝ) : ℝ) := by
    rw [show (103 / 400 : ℝ) - Real.pi * Real.exp (823 / 800 : ℝ) =
      -(Real.pi * Real.exp (823 / 800 : ℝ) - (103 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (21999522047867091 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (21999522047867091 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell823_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (823 / 1600 : ℝ) (103 / 200 : ℝ)) :
    (499613009 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1016049151 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell823_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell823_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell824_leftExp :
    (14005329173 / 5000000000 : ℝ) ≤ Real.exp (103 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (103 / 100 : ℝ) (129088890061 / 125000000000 : ℝ)
    (14005329173 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell824_rightExp :
    Real.exp (33 / 32 : ℝ) ≤ (7011423391 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (33 / 32 : ℝ) (206550292311 / 200000000000 : ℝ)
    (7011423391 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell824_denomUpper :
    Real.exp (21383288645201863 / 2500000000000000 : ℝ) ≤ (51839130135023 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21383288645201863 / 2500000000000000 : ℝ) (1306420700583
    / 1000000000000 : ℝ) (51839130135023 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell824_denomLower :
    (51255520610207 / 10000000000 : ℝ) ≤ Real.exp (5338745948407927 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5338745948407927 / 625000000000000 : ℝ) (163244819599 /
    125000000000 : ℝ) (51255520610207 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell824_product_lower :
    (5499878760907927 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (103 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell824_leftExp
    (by norm_num : (0 : ℝ) ≤ (14005329173 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell824_product_upper :
    Real.pi * Real.exp (33 / 32 : ℝ) ≤ (22027038645201863 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell824_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell824_endpointLower :
    (991326463 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (103 / 200 : ℝ) (33 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5499878760907927 / 625000000000000 : ℝ) (Real.pi * Real.exp (103 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell824_product_lower
  have hD : Real.exp (Real.pi * Real.exp (33 / 32 : ℝ) - (103 / 400 : ℝ)) ≤
      (51839130135023 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell824_denomUpper
    linarith [hpThetaJensenCell824_product_upper]
  have hi : (1 / (51839130135023 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (33 / 32 : ℝ) - (103 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (51839130135023 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (51839130135023 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((103 / 400 : ℝ) - Real.pi * Real.exp (33 / 32 : ℝ)) := by
    rw [show (103 / 400 : ℝ) - Real.pi * Real.exp (33 / 32 : ℝ) =
      -(Real.pi * Real.exp (33 / 32 : ℝ) - (103 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (103 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (103 / 100 : ℝ)) := by
    have h := hpThetaJensenCell824_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (51839130135023 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell824_endpointUpper :
    hpThetaJensenKernelEndpointUpper (103 / 200 : ℝ) (33 / 64 : ℝ) ≤ (1008030071 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (33 / 32 : ℝ)) (22027038645201863 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (33 / 64 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell824_product_upper
  have hD : (51255520610207 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (103 / 100 : ℝ) - (33 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell824_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell824_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (103 / 100 : ℝ) - (33 / 128 : ℝ)) ≤
      (1 / (51255520610207 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (51255520610207 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((33 / 128 : ℝ) - Real.pi * Real.exp (103 / 100 : ℝ)) ≤
      (2 / (51255520610207 / 10000000000 : ℝ) : ℝ) := by
    rw [show (33 / 128 : ℝ) - Real.pi * Real.exp (103 / 100 : ℝ) =
      -(Real.pi * Real.exp (103 / 100 : ℝ) - (33 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (22027038645201863 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (22027038645201863 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell824_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (103 / 200 : ℝ) (33 / 64 : ℝ)) :
    (991326463 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1008030071 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell824_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell824_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell825_leftExp :
    (14022846781 / 5000000000 : ℝ) ≤ Real.exp (33 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (33 / 32 : ℝ) (516375730777 / 500000000000 : ℝ)
    (14022846781 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell825_rightExp :
    Real.exp (413 / 400 : ℝ) ≤ (140403863 / 50000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (413 / 400 : ℝ) (1032791804197 / 1000000000000 : ℝ)
    (140403863 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell825_denomUpper :
    Real.exp (428201168173759 / 50000000000000 : ℝ) ≤ (1637412537187 / 312500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (428201168173759 / 50000000000000 : ℝ) (1306857930897 /
    1000000000000 : ℝ) (1637412537187 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell825_denomLower :
    (10361319094413 / 2000000000 : ℝ) ≤ Real.exp (5345429783051919 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5345429783051919 / 625000000000000 : ℝ) (32659876757 /
    25000000000 : ℝ) (10361319094413 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell825_product_lower :
    (5506757908051919 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (33 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell825_leftExp
    (by norm_num : (0 : ℝ) ≤ (14022846781 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell825_product_upper :
    Real.pi * Real.exp (413 / 400 : ℝ) ≤ (441091793173759 / 50000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell825_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell825_endpointLower :
    (12293443 / 125000000 : ℝ) ≤ hpThetaTraceEndpointLower (33 / 64 : ℝ) (413 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5506757908051919 / 625000000000000 : ℝ) (Real.pi * Real.exp (33 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell825_product_lower
  have hD : Real.exp (Real.pi * Real.exp (413 / 400 : ℝ) - (33 / 128 : ℝ)) ≤
      (1637412537187 / 312500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell825_denomUpper
    linarith [hpThetaJensenCell825_product_upper]
  have hi : (1 / (1637412537187 / 312500000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (413 / 400 : ℝ) - (33 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1637412537187 / 312500000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1637412537187 / 312500000 : ℝ) : ℝ) ≤
      2 * Real.exp ((33 / 128 : ℝ) - Real.pi * Real.exp (413 / 400 : ℝ)) := by
    rw [show (33 / 128 : ℝ) - Real.pi * Real.exp (413 / 400 : ℝ) =
      -(Real.pi * Real.exp (413 / 400 : ℝ) - (33 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (33 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (33 / 32 : ℝ)) := by
    have h := hpThetaJensenCell825_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1637412537187 / 312500000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell825_endpointUpper :
    hpThetaJensenKernelEndpointUpper (33 / 64 : ℝ) (413 / 800 : ℝ) ≤ (62503759 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (413 / 400 : ℝ)) (441091793173759 / 50000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (413 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell825_product_upper
  have hD : (10361319094413 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (33 / 32 : ℝ) - (413 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell825_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell825_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (33 / 32 : ℝ) - (413 / 1600 : ℝ)) ≤
      (1 / (10361319094413 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (10361319094413 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((413 / 1600 : ℝ) - Real.pi * Real.exp (33 / 32 : ℝ)) ≤
      (2 / (10361319094413 / 2000000000 : ℝ) : ℝ) := by
    rw [show (413 / 1600 : ℝ) - Real.pi * Real.exp (33 / 32 : ℝ) =
      -(Real.pi * Real.exp (33 / 32 : ℝ) - (413 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (441091793173759 / 50000000000000 : ℝ) ^ 2 - 6 *
      (441091793173759 / 50000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell825_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (33 / 64 : ℝ) (413 / 800 : ℝ)) :
    (12293443 / 125000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (62503759 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell825_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell825_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell826_leftExp :
    (28080772599 / 10000000000 : ℝ) ≤ Real.exp (413 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (413 / 400 : ℝ) (258197951049 / 250000000000 : ℝ)
    (28080772599 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell826_rightExp :
    Real.exp (827 / 800 : ℝ) ≤ (28115895513 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (827 / 800 : ℝ) (516416074207 / 500000000000 : ℝ)
    (28115895513 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell826_denomUpper :
    Real.exp (85747450532372209 / 10000000000000000 : ℝ) ≤ (26481005084163 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (85747450532372209 / 10000000000000000 : ℝ) (52291834827
    / 40000000000 : ℝ) (26481005084163 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell826_denomLower :
    (52364316110239 / 10000000000 : ℝ) ≤ Real.exp (10704244443854701 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10704244443854701 / 1250000000000000 : ℝ) (653416145943
    / 500000000000 : ℝ) (52364316110239 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell826_product_lower :
    (11027291318854701 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (413 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell826_leftExp
    (by norm_num : (0 : ℝ) ≤ (28080772599 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell826_product_upper :
    Real.pi * Real.exp (827 / 800 : ℝ) ≤ (88328700532372209 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell826_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell826_endpointLower :
    (15244887 / 156250000 : ℝ) ≤ hpThetaTraceEndpointLower (413 / 800 : ℝ) (827 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11027291318854701 / 1250000000000000 : ℝ) (Real.pi * Real.exp (413 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell826_product_lower
  have hD : Real.exp (Real.pi * Real.exp (827 / 800 : ℝ) - (413 / 1600 : ℝ)) ≤
      (26481005084163 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell826_denomUpper
    linarith [hpThetaJensenCell826_product_upper]
  have hi : (1 / (26481005084163 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (827 / 800 : ℝ) - (413 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (26481005084163 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (26481005084163 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((413 / 1600 : ℝ) - Real.pi * Real.exp (827 / 800 : ℝ)) := by
    rw [show (413 / 1600 : ℝ) - Real.pi * Real.exp (827 / 800 : ℝ) =
      -(Real.pi * Real.exp (827 / 800 : ℝ) - (413 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (413 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (413 / 400 : ℝ)) := by
    have h := hpThetaJensenCell826_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (26481005084163 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell826_endpointUpper :
    hpThetaJensenKernelEndpointUpper (413 / 800 : ℝ) (827 / 1600 : ℝ) ≤ (99213919 / 1000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (827 / 800 : ℝ)) (88328700532372209 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (827 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell826_product_upper
  have hD : (52364316110239 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (413 / 400 : ℝ) - (827 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell826_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell826_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (413 / 400 : ℝ) - (827 / 3200 : ℝ)) ≤
      (1 / (52364316110239 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (52364316110239 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((827 / 3200 : ℝ) - Real.pi * Real.exp (413 / 400 : ℝ)) ≤
      (2 / (52364316110239 / 10000000000 : ℝ) : ℝ) := by
    rw [show (827 / 3200 : ℝ) - Real.pi * Real.exp (413 / 400 : ℝ) =
      -(Real.pi * Real.exp (413 / 400 : ℝ) - (827 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (88328700532372209 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (88328700532372209 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell826_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (413 / 800 : ℝ) (827 / 1600 : ℝ)) :
    (15244887 / 156250000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (99213919 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell826_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell826_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell827_leftExp :
    (28115895511 / 10000000000 : ℝ) ≤ Real.exp (827 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (827 / 800 : ℝ) (1032832148413 / 1000000000000 : ℝ)
    (28115895511 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell827_rightExp :
    Real.exp (207 / 200 : ℝ) ≤ (28151062357 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (207 / 200 : ℝ) (8069316361 / 7812500000 : ℝ)
    (28151062357 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell827_denomUpper :
    Real.exp (85854805443314701 / 10000000000000000 : ℝ) ≤ (53533646263401 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (85854805443314701 / 10000000000000000 : ℝ) (52309380849
    / 40000000000 : ℝ) (53533646263401 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell827_denomLower :
    (3308048150359 / 625000000 : ℝ) ≤ Real.exp (10717646551274189 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10717646551274189 / 1250000000000000 : ℝ) (326817555729
    / 250000000000 : ℝ) (3308048150359 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell827_product_lower :
    (11041084051274189 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (827 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell827_leftExp
    (by norm_num : (0 : ℝ) ≤ (28115895511 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell827_product_upper :
    Real.pi * Real.exp (207 / 200 : ℝ) ≤ (88439180443314701 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell827_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell827_endpointLower :
    (967918269 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (827 / 1600 : ℝ) (207 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11041084051274189 / 1250000000000000 : ℝ) (Real.pi * Real.exp (827 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell827_product_lower
  have hD : Real.exp (Real.pi * Real.exp (207 / 200 : ℝ) - (827 / 3200 : ℝ)) ≤
      (53533646263401 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell827_denomUpper
    linarith [hpThetaJensenCell827_product_upper]
  have hi : (1 / (53533646263401 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (207 / 200 : ℝ) - (827 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (53533646263401 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (53533646263401 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((827 / 3200 : ℝ) - Real.pi * Real.exp (207 / 200 : ℝ)) := by
    rw [show (827 / 3200 : ℝ) - Real.pi * Real.exp (207 / 200 : ℝ) =
      -(Real.pi * Real.exp (207 / 200 : ℝ) - (827 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (827 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (827 / 800 : ℝ)) := by
    have h := hpThetaJensenCell827_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (53533646263401 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell827_endpointUpper :
    hpThetaJensenKernelEndpointUpper (827 / 1600 : ℝ) (207 / 400 : ℝ) ≤ (984267027 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (207 / 200 : ℝ)) (88439180443314701 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (207 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell827_product_upper
  have hD : (3308048150359 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (827 / 800 : ℝ) - (207 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell827_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell827_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (827 / 800 : ℝ) - (207 / 800 : ℝ)) ≤
      (1 / (3308048150359 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3308048150359 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((207 / 800 : ℝ) - Real.pi * Real.exp (827 / 800 : ℝ)) ≤
      (2 / (3308048150359 / 625000000 : ℝ) : ℝ) := by
    rw [show (207 / 800 : ℝ) - Real.pi * Real.exp (827 / 800 : ℝ) =
      -(Real.pi * Real.exp (827 / 800 : ℝ) - (207 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (88439180443314701 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (88439180443314701 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell827_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (827 / 1600 : ℝ) (207 / 400 : ℝ)) :
    (967918269 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (984267027 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell827_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell827_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell828_leftExp :
    (5630212471 / 2000000000 : ℝ) ≤ Real.exp (207 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (207 / 200 : ℝ) (1032872494207 / 1000000000000 : ℝ)
    (5630212471 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell828_rightExp :
    Real.exp (829 / 800 : ℝ) ≤ (28186273187 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (829 / 800 : ℝ) (516456420789 / 500000000000 : ℝ)
    (28186273187 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell828_denomUpper :
    Real.exp (85962298540366891 / 10000000000000000 : ℝ) ≤ (54112199962347 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (85962298540366891 / 10000000000000000 : ℝ)
    (1308173883871 / 1000000000000 : ℝ) (54112199962347 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell828_denomLower :
    (53500047544613 / 10000000000 : ℝ) ≤ Real.exp (2146213182149229 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2146213182149229 / 250000000000000 : ℝ) (326927216179 /
    250000000000 : ℝ) (53500047544613 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell828_product_lower :
    (2210978807149229 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (207 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell828_leftExp
    (by norm_num : (0 : ℝ) ≤ (5630212471 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell828_product_upper :
    Real.pi * Real.exp (829 / 800 : ℝ) ≤ (88549798540366891 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell828_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell828_endpointLower :
    (240052941 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (207 / 400 : ℝ) (829 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2210978807149229 / 250000000000000 : ℝ) (Real.pi * Real.exp (207 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell828_product_lower
  have hD : Real.exp (Real.pi * Real.exp (829 / 800 : ℝ) - (207 / 800 : ℝ)) ≤
      (54112199962347 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell828_denomUpper
    linarith [hpThetaJensenCell828_product_upper]
  have hi : (1 / (54112199962347 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (829 / 800 : ℝ) - (207 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (54112199962347 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (54112199962347 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((207 / 800 : ℝ) - Real.pi * Real.exp (829 / 800 : ℝ)) := by
    rw [show (207 / 800 : ℝ) - Real.pi * Real.exp (829 / 800 : ℝ) =
      -(Real.pi * Real.exp (829 / 800 : ℝ) - (207 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (207 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (207 / 200 : ℝ)) := by
    have h := hpThetaJensenCell828_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (54112199962347 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell828_endpointUpper :
    hpThetaJensenKernelEndpointUpper (207 / 400 : ℝ) (829 / 1600 : ℝ) ≤ (39057739 / 400000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (829 / 800 : ℝ)) (88549798540366891 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (829 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell828_product_upper
  have hD : (53500047544613 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (207 / 200 : ℝ) - (829 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell828_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell828_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (207 / 200 : ℝ) - (829 / 3200 : ℝ)) ≤
      (1 / (53500047544613 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (53500047544613 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((829 / 3200 : ℝ) - Real.pi * Real.exp (207 / 200 : ℝ)) ≤
      (2 / (53500047544613 / 10000000000 : ℝ) : ℝ) := by
    rw [show (829 / 3200 : ℝ) - Real.pi * Real.exp (207 / 200 : ℝ) =
      -(Real.pi * Real.exp (207 / 200 : ℝ) - (829 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (88549798540366891 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (88549798540366891 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell828_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (207 / 400 : ℝ) (829 / 1600 : ℝ)) :
    (240052941 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (39057739 / 400000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell828_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell828_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell829_leftExp :
    (5637254637 / 2000000000 : ℝ) ≤ Real.exp (829 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (829 / 800 : ℝ) (1032912841577 / 1000000000000 : ℝ)
    (5637254637 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell829_rightExp :
    Real.exp (83 / 80 : ℝ) ≤ (14110764029 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (83 / 80 : ℝ) (258238297631 / 250000000000 : ℝ)
    (14110764029 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell829_denomUpper :
    Real.exp (43034964998158197 / 5000000000000000 : ℝ) ≤ (13674440761619 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (43034964998158197 / 5000000000000000 : ℝ) (654306979969
    / 500000000000 : ℝ) (13674440761619 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell829_denomLower :
    (54078237943093 / 10000000000 : ℝ) ≤ Real.exp (2148900508695263 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2148900508695263 / 250000000000000 : ℝ) (1308148218599 /
    1000000000000 : ℝ) (54078237943093 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell829_product_lower :
    (2213744258695263 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (829 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell829_leftExp
    (by norm_num : (0 : ℝ) ≤ (5637254637 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell829_product_upper :
    Real.pi * Real.exp (83 / 80 : ℝ) ≤ (44330277498158197 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell829_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell829_endpointLower :
    (952553071 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (829 / 1600 : ℝ) (83 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2213744258695263 / 250000000000000 : ℝ) (Real.pi * Real.exp (829 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell829_product_lower
  have hD : Real.exp (Real.pi * Real.exp (83 / 80 : ℝ) - (829 / 3200 : ℝ)) ≤
      (13674440761619 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell829_denomUpper
    linarith [hpThetaJensenCell829_product_upper]
  have hi : (1 / (13674440761619 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (83 / 80 : ℝ) - (829 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (13674440761619 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (13674440761619 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((829 / 3200 : ℝ) - Real.pi * Real.exp (83 / 80 : ℝ)) := by
    rw [show (829 / 3200 : ℝ) - Real.pi * Real.exp (83 / 80 : ℝ) =
      -(Real.pi * Real.exp (83 / 80 : ℝ) - (829 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (829 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (829 / 800 : ℝ)) := by
    have h := hpThetaJensenCell829_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (13674440761619 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell829_endpointUpper :
    hpThetaJensenKernelEndpointUpper (829 / 1600 : ℝ) (83 / 160 : ℝ) ≤ (968668351 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (83 / 80 : ℝ)) (44330277498158197 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (83 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell829_product_upper
  have hD : (54078237943093 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (829 / 800 : ℝ) - (83 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell829_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell829_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (829 / 800 : ℝ) - (83 / 320 : ℝ)) ≤
      (1 / (54078237943093 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (54078237943093 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((83 / 320 : ℝ) - Real.pi * Real.exp (829 / 800 : ℝ)) ≤
      (2 / (54078237943093 / 10000000000 : ℝ) : ℝ) := by
    rw [show (83 / 320 : ℝ) - Real.pi * Real.exp (829 / 800 : ℝ) =
      -(Real.pi * Real.exp (829 / 800 : ℝ) - (83 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (44330277498158197 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (44330277498158197 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell829_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (829 / 1600 : ℝ) (83 / 160 : ℝ)) :
    (952553071 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (968668351 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell829_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell829_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell830_leftExp :
    (28221528057 / 10000000000 : ℝ) ≤ Real.exp (83 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (83 / 80 : ℝ) (1032953190523 / 1000000000000 : ℝ)
    (28221528057 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell830_rightExp :
    Real.exp (831 / 800 : ℝ) ≤ (14128413513 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (831 / 800 : ℝ) (516496770523 / 500000000000 : ℝ)
    (14128413513 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell830_denomUpper :
    Real.exp (43088849993546209 / 5000000000000000 : ℝ) ≤ (27645214315649 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (43088849993546209 / 5000000000000000 : ℝ) (1309054750767
    / 1000000000000 : ℝ) (27645214315649 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell830_denomLower :
    (10932686667653 / 2000000000 : ℝ) ≤ Real.exp (10757956471455843 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10757956471455843 / 1250000000000000 : ℝ) (13085882859 /
    10000000000 : ℝ) (10932686667653 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell830_product_lower :
    (11082565846455843 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (83 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell830_leftExp
    (by norm_num : (0 : ℝ) ≤ (28221528057 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell830_product_upper :
    Real.pi * Real.exp (831 / 800 : ℝ) ≤ (44385724993546209 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell830_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell830_endpointLower :
    (944942011 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (83 / 160 : ℝ) (831 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11082565846455843 / 1250000000000000 : ℝ) (Real.pi * Real.exp (83 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell830_product_lower
  have hD : Real.exp (Real.pi * Real.exp (831 / 800 : ℝ) - (83 / 320 : ℝ)) ≤
      (27645214315649 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell830_denomUpper
    linarith [hpThetaJensenCell830_product_upper]
  have hi : (1 / (27645214315649 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (831 / 800 : ℝ) - (83 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (27645214315649 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (27645214315649 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((83 / 320 : ℝ) - Real.pi * Real.exp (831 / 800 : ℝ)) := by
    rw [show (83 / 320 : ℝ) - Real.pi * Real.exp (831 / 800 : ℝ) =
      -(Real.pi * Real.exp (831 / 800 : ℝ) - (83 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (83 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (83 / 80 : ℝ)) := by
    have h := hpThetaJensenCell830_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (27645214315649 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell830_endpointUpper :
    hpThetaJensenKernelEndpointUpper (83 / 160 : ℝ) (831 / 1600 : ℝ) ≤ (38437659 / 400000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (831 / 800 : ℝ)) (44385724993546209 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (831 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell830_product_upper
  have hD : (10932686667653 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (83 / 80 : ℝ) - (831 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell830_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell830_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (83 / 80 : ℝ) - (831 / 3200 : ℝ)) ≤
      (1 / (10932686667653 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (10932686667653 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((831 / 3200 : ℝ) - Real.pi * Real.exp (83 / 80 : ℝ)) ≤
      (2 / (10932686667653 / 2000000000 : ℝ) : ℝ) := by
    rw [show (831 / 3200 : ℝ) - Real.pi * Real.exp (83 / 80 : ℝ) =
      -(Real.pi * Real.exp (83 / 80 : ℝ) - (831 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (44385724993546209 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (44385724993546209 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell830_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (83 / 160 : ℝ) (831 / 1600 : ℝ)) :
    (944942011 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (38437659 / 400000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell830_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell830_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell831_leftExp :
    (1766051689 / 625000000 : ℝ) ≤ Real.exp (831 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (831 / 800 : ℝ) (206598708209 / 200000000000 : ℝ)
    (1766051689 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell831_rightExp :
    Real.exp (26 / 25 : ℝ) ≤ (884130317 / 312500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (26 / 25 : ℝ) (129129236643 / 125000000000 : ℝ)
    (884130317 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell831_denomUpper :
    Real.exp (2696425271224981 / 312500000000000 : ℝ) ≤ (55890291112539 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (2696425271224981 / 312500000000000 : ℝ) (65474812883 /
    50000000000 : ℝ) (55890291112539 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell831_denomLower :
    (55255726737649 / 10000000000 : ℝ) ≤ Real.exp (673214232218611 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (673214232218611 / 78125000000000 : ℝ) (1309029067923 /
    1000000000000 : ℝ) (55255726737649 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell831_product_lower :
    (693526732218611 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (831 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell831_leftExp
    (by norm_num : (0 : ℝ) ≤ (1766051689 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell831_product_upper :
    Real.pi * Real.exp (26 / 25 : ℝ) ≤ (2777577614974981 / 312500000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell831_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell831_endpointLower :
    (234344601 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (831 / 1600 : ℝ) (13 / 25 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (693526732218611 / 78125000000000 : ℝ) (Real.pi * Real.exp (831 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell831_product_lower
  have hD : Real.exp (Real.pi * Real.exp (26 / 25 : ℝ) - (831 / 3200 : ℝ)) ≤
      (55890291112539 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell831_denomUpper
    linarith [hpThetaJensenCell831_product_upper]
  have hi : (1 / (55890291112539 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (26 / 25 : ℝ) - (831 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (55890291112539 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (55890291112539 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((831 / 3200 : ℝ) - Real.pi * Real.exp (26 / 25 : ℝ)) := by
    rw [show (831 / 3200 : ℝ) - Real.pi * Real.exp (26 / 25 : ℝ) =
      -(Real.pi * Real.exp (26 / 25 : ℝ) - (831 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (831 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (831 / 800 : ℝ)) := by
    have h := hpThetaJensenCell831_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (55890291112539 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell831_endpointUpper :
    hpThetaJensenKernelEndpointUpper (831 / 1600 : ℝ) (13 / 25 : ℝ) ≤ (119157833 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (26 / 25 : ℝ)) (2777577614974981 / 312500000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (13 / 25 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell831_product_upper
  have hD : (55255726737649 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (831 / 800 : ℝ) - (13 / 50 : ℝ)) := by
    apply le_trans hpThetaJensenCell831_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell831_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (831 / 800 : ℝ) - (13 / 50 : ℝ)) ≤
      (1 / (55255726737649 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (55255726737649 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((13 / 50 : ℝ) - Real.pi * Real.exp (831 / 800 : ℝ)) ≤
      (2 / (55255726737649 / 10000000000 : ℝ) : ℝ) := by
    rw [show (13 / 50 : ℝ) - Real.pi * Real.exp (831 / 800 : ℝ) =
      -(Real.pi * Real.exp (831 / 800 : ℝ) - (13 / 50 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2777577614974981 / 312500000000000 : ℝ) ^ 2 - 6 *
      (2777577614974981 / 312500000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell831_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (831 / 1600 : ℝ) (13 / 25 : ℝ)) :
    (234344601 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (119157833 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell831_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell831_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell832_leftExp :
    (14146085071 / 5000000000 : ℝ) ≤ Real.exp (26 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (26 / 25 : ℝ) (1033033893143 / 1000000000000 : ℝ)
    (14146085071 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell832_rightExp :
    Real.exp (833 / 800 : ℝ) ≤ (2832755747 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (833 / 800 : ℝ) (1033074246819 / 1000000000000 : ℝ)
    (2832755747 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell832_denomUpper :
    Real.exp (8639365625484971 / 1000000000000000 : ℝ) ≤ (56497446334117 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8639365625484971 / 1000000000000000 : ℝ) (1309938481989
    / 1000000000000 : ℝ) (56497446334117 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell832_denomLower :
    (27927606265593 / 5000000000 : ℝ) ≤ Real.exp (5392458148796629 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5392458148796629 / 625000000000000 : ℝ) (130947056601 /
    100000000000 : ℝ) (27927606265593 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell832_product_lower :
    (5555153461296629 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (26 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell832_leftExp
    (by norm_num : (0 : ℝ) ≤ (14146085071 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell832_product_upper :
    Real.pi * Real.exp (833 / 800 : ℝ) ≤ (8899365625484971 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell832_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell832_endpointLower :
    (929862069 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (13 / 25 : ℝ) (833 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5555153461296629 / 625000000000000 : ℝ) (Real.pi * Real.exp (26 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell832_product_lower
  have hD : Real.exp (Real.pi * Real.exp (833 / 800 : ℝ) - (13 / 50 : ℝ)) ≤
      (56497446334117 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell832_denomUpper
    linarith [hpThetaJensenCell832_product_upper]
  have hi : (1 / (56497446334117 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (833 / 800 : ℝ) - (13 / 50 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (56497446334117 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (56497446334117 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((13 / 50 : ℝ) - Real.pi * Real.exp (833 / 800 : ℝ)) := by
    rw [show (13 / 50 : ℝ) - Real.pi * Real.exp (833 / 800 : ℝ) =
      -(Real.pi * Real.exp (833 / 800 : ℝ) - (13 / 50 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (26 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (26 / 25 : ℝ)) := by
    have h := hpThetaJensenCell832_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (56497446334117 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell832_endpointUpper :
    hpThetaJensenKernelEndpointUpper (13 / 25 : ℝ) (833 / 1600 : ℝ) ≤ (945631737 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (833 / 800 : ℝ)) (8899365625484971 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (833 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell832_product_upper
  have hD : (27927606265593 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (26 / 25 : ℝ) - (833 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell832_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell832_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (26 / 25 : ℝ) - (833 / 3200 : ℝ)) ≤
      (1 / (27927606265593 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (27927606265593 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((833 / 3200 : ℝ) - Real.pi * Real.exp (26 / 25 : ℝ)) ≤
      (2 / (27927606265593 / 5000000000 : ℝ) : ℝ) := by
    rw [show (833 / 3200 : ℝ) - Real.pi * Real.exp (26 / 25 : ℝ) =
      -(Real.pi * Real.exp (26 / 25 : ℝ) - (833 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8899365625484971 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (8899365625484971 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell832_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (13 / 25 : ℝ) (833 / 1600 : ℝ)) :
    (929862069 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (945631737 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell832_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell832_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell833_leftExp :
    (7081889367 / 2500000000 : ℝ) ≤ Real.exp (833 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (833 / 800 : ℝ) (516537123409 / 500000000000 : ℝ)
    (7081889367 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell833_rightExp :
    Real.exp (417 / 400 : ℝ) ≤ (28362989057 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (417 / 400 : ℝ) (103311460207 / 100000000000 : ℝ)
    (28362989057 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell833_denomUpper :
    Real.exp (86501842880547801 / 10000000000000000 : ℝ) ≤ (11422398285391 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (86501842880547801 / 10000000000000000 : ℝ) (655190712531
    / 500000000000 : ℝ) (11422398285391 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell833_denomLower :
    (28230993241257 / 5000000000 : ℝ) ≤ Real.exp (2699605560031533 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2699605560031533 / 312500000000000 : ℝ) (654956390759 /
    500000000000 : ℝ) (28230993241257 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell833_product_lower :
    (2781050872531533 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (833 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell833_leftExp
    (by norm_num : (0 : ℝ) ≤ (7081889367 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell833_product_upper :
    Real.pi * Real.exp (417 / 400 : ℝ) ≤ (89104967880547801 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell833_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell833_endpointLower :
    (36895713 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (833 / 1600 : ℝ) (417 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2781050872531533 / 312500000000000 : ℝ) (Real.pi * Real.exp (833 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell833_product_lower
  have hD : Real.exp (Real.pi * Real.exp (417 / 400 : ℝ) - (833 / 3200 : ℝ)) ≤
      (11422398285391 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell833_denomUpper
    linarith [hpThetaJensenCell833_product_upper]
  have hi : (1 / (11422398285391 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (417 / 400 : ℝ) - (833 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (11422398285391 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (11422398285391 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((833 / 3200 : ℝ) - Real.pi * Real.exp (417 / 400 : ℝ)) := by
    rw [show (833 / 3200 : ℝ) - Real.pi * Real.exp (417 / 400 : ℝ) =
      -(Real.pi * Real.exp (417 / 400 : ℝ) - (833 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (833 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (833 / 800 : ℝ)) := by
    have h := hpThetaJensenCell833_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (11422398285391 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell833_endpointUpper :
    hpThetaJensenKernelEndpointUpper (833 / 1600 : ℝ) (417 / 800 : ℝ) ≤ (938048511 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (417 / 400 : ℝ)) (89104967880547801 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (417 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell833_product_upper
  have hD : (28230993241257 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (833 / 800 : ℝ) - (417 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell833_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell833_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (833 / 800 : ℝ) - (417 / 1600 : ℝ)) ≤
      (1 / (28230993241257 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (28230993241257 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((417 / 1600 : ℝ) - Real.pi * Real.exp (833 / 800 : ℝ)) ≤
      (2 / (28230993241257 / 5000000000 : ℝ) : ℝ) := by
    rw [show (417 / 1600 : ℝ) - Real.pi * Real.exp (833 / 800 : ℝ) =
      -(Real.pi * Real.exp (833 / 800 : ℝ) - (417 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (89104967880547801 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (89104967880547801 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell833_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (833 / 1600 : ℝ) (417 / 800 : ℝ)) :
    (36895713 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (938048511 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell833_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell833_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell834_leftExp :
    (5672597811 / 2000000000 : ℝ) ≤ Real.exp (417 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (417 / 400 : ℝ) (1033114602069 / 1000000000000 : ℝ)
    (5672597811 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell834_rightExp :
    Real.exp (167 / 160 : ℝ) ≤ (88745203 / 31250000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (167 / 160 : ℝ) (1033154958897 / 1000000000000 : ℝ)
    (88745203 / 31250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell834_denomUpper :
    Real.exp (270656777278379 / 31250000000000 : ℝ) ≤ (57734024952177 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (270656777278379 / 31250000000000 : ℝ) (1310825088213 /
    1000000000000 : ℝ) (57734024952177 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell834_denomLower :
    (11415229132303 / 2000000000 : ℝ) ≤ Real.exp (2162389112781889 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2162389112781889 / 250000000000000 : ℝ) (262071143151 /
    200000000000 : ℝ) (11415229132303 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell834_product_lower :
    (2227623487781889 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (417 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell834_leftExp
    (by norm_num : (0 : ℝ) ≤ (5672597811 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell834_product_upper :
    Real.pi * Real.exp (167 / 160 : ℝ) ≤ (278801308528379 / 31250000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell834_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell834_endpointLower :
    (228742623 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (417 / 800 : ℝ) (167 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2227623487781889 / 250000000000000 : ℝ) (Real.pi * Real.exp (417 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell834_product_lower
  have hD : Real.exp (Real.pi * Real.exp (167 / 160 : ℝ) - (417 / 1600 : ℝ)) ≤
      (57734024952177 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell834_denomUpper
    linarith [hpThetaJensenCell834_product_upper]
  have hi : (1 / (57734024952177 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (167 / 160 : ℝ) - (417 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (57734024952177 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (57734024952177 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((417 / 1600 : ℝ) - Real.pi * Real.exp (167 / 160 : ℝ)) := by
    rw [show (417 / 1600 : ℝ) - Real.pi * Real.exp (167 / 160 : ℝ) =
      -(Real.pi * Real.exp (167 / 160 : ℝ) - (417 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (417 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (417 / 400 : ℝ)) := by
    have h := hpThetaJensenCell834_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (57734024952177 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell834_endpointUpper :
    hpThetaJensenKernelEndpointUpper (417 / 800 : ℝ) (167 / 320 : ℝ) ≤ (930512803 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (167 / 160 : ℝ)) (278801308528379 / 31250000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (167 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell834_product_upper
  have hD : (11415229132303 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (417 / 400 : ℝ) - (167 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell834_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell834_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (417 / 400 : ℝ) - (167 / 640 : ℝ)) ≤
      (1 / (11415229132303 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (11415229132303 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((167 / 640 : ℝ) - Real.pi * Real.exp (417 / 400 : ℝ)) ≤
      (2 / (11415229132303 / 2000000000 : ℝ) : ℝ) := by
    rw [show (167 / 640 : ℝ) - Real.pi * Real.exp (417 / 400 : ℝ) =
      -(Real.pi * Real.exp (417 / 400 : ℝ) - (167 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (278801308528379 / 31250000000000 : ℝ) ^ 2 - 6 *
      (278801308528379 / 31250000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell834_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (417 / 800 : ℝ) (167 / 320 : ℝ)) :
    (228742623 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (930512803 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell834_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell834_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell835_leftExp :
    (14199232479 / 5000000000 : ℝ) ≤ Real.exp (167 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (167 / 160 : ℝ) (64572184931 / 62500000000 : ℝ)
    (14199232479 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell835_rightExp :
    Real.exp (209 / 200 : ℝ) ≤ (28433985237 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (209 / 200 : ℝ) (1033195317301 / 1000000000000 : ℝ)
    (28433985237 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell835_denomUpper :
    Real.exp (86718633982662541 / 10000000000000000 : ℝ) ≤ (58363646951393 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (86718633982662541 / 10000000000000000 : ℝ)
    (1311269472821 / 1000000000000 : ℝ) (58363646951393 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell835_denomLower :
    (28848894285097 / 5000000000 : ℝ) ≤ Real.exp (5412743145270821 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5412743145270821 / 625000000000000 : ℝ) (1310799370057 /
    1000000000000 : ℝ) (28848894285097 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell835_product_lower :
    (5576024395270821 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (167 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell835_leftExp
    (by norm_num : (0 : ℝ) ≤ (14199232479 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell835_product_upper :
    Real.pi * Real.exp (209 / 200 : ℝ) ≤ (89328008982662541 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell835_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell835_endpointLower :
    (907594887 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (167 / 320 : ℝ) (209 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5576024395270821 / 625000000000000 : ℝ) (Real.pi * Real.exp (167 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell835_product_lower
  have hD : Real.exp (Real.pi * Real.exp (209 / 200 : ℝ) - (167 / 640 : ℝ)) ≤
      (58363646951393 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell835_denomUpper
    linarith [hpThetaJensenCell835_product_upper]
  have hi : (1 / (58363646951393 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (209 / 200 : ℝ) - (167 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (58363646951393 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (58363646951393 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((167 / 640 : ℝ) - Real.pi * Real.exp (209 / 200 : ℝ)) := by
    rw [show (167 / 640 : ℝ) - Real.pi * Real.exp (209 / 200 : ℝ) =
      -(Real.pi * Real.exp (209 / 200 : ℝ) - (167 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (167 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (167 / 160 : ℝ)) := by
    have h := hpThetaJensenCell835_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (58363646951393 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell835_endpointUpper :
    hpThetaJensenKernelEndpointUpper (167 / 320 : ℝ) (209 / 400 : ℝ) ≤ (923024431 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (209 / 200 : ℝ)) (89328008982662541 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (209 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell835_product_upper
  have hD : (28848894285097 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (167 / 160 : ℝ) - (209 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell835_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell835_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (167 / 160 : ℝ) - (209 / 800 : ℝ)) ≤
      (1 / (28848894285097 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (28848894285097 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((209 / 800 : ℝ) - Real.pi * Real.exp (167 / 160 : ℝ)) ≤
      (2 / (28848894285097 / 5000000000 : ℝ) : ℝ) := by
    rw [show (209 / 800 : ℝ) - Real.pi * Real.exp (167 / 160 : ℝ) =
      -(Real.pi * Real.exp (167 / 160 : ℝ) - (209 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (89328008982662541 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (89328008982662541 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell835_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (167 / 320 : ℝ) (209 / 400 : ℝ)) :
    (907594887 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (923024431 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell835_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell835_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell836_leftExp :
    (5686797047 / 2000000000 : ℝ) ≤ Real.exp (209 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (209 / 200 : ℝ) (10331953173 / 10000000000 : ℝ)
    (5686797047 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell836_rightExp :
    Real.exp (837 / 800 : ℝ) ≤ (28469549943 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (837 / 800 : ℝ) (516617838641 / 500000000000 : ℝ)
    (28469549943 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell836_denomUpper :
    Real.exp (86827238814079199 / 10000000000000000 : ℝ) ≤ (29500479423993 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (86827238814079199 / 10000000000000000 : ℝ) (5123885079 /
    3906250000 : ℝ) (29500479423993 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell836_denomLower :
    (7290876897889 / 1250000000 : ℝ) ≤ Real.exp (2167808888559853 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2167808888559853 / 250000000000000 : ℝ) (6556218729 /
    5000000000 : ℝ) (7290876897889 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell836_product_lower :
    (2233199513559853 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (209 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell836_leftExp
    (by norm_num : (0 : ℝ) ≤ (5686797047 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell836_product_upper :
    Real.pi * Real.exp (837 / 800 : ℝ) ≤ (89439738814079199 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell836_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell836_endpointLower :
    (90026583 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (209 / 400 : ℝ) (837 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2233199513559853 / 250000000000000 : ℝ) (Real.pi * Real.exp (209 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell836_product_lower
  have hD : Real.exp (Real.pi * Real.exp (837 / 800 : ℝ) - (209 / 800 : ℝ)) ≤
      (29500479423993 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell836_denomUpper
    linarith [hpThetaJensenCell836_product_upper]
  have hi : (1 / (29500479423993 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (837 / 800 : ℝ) - (209 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (29500479423993 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (29500479423993 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((209 / 800 : ℝ) - Real.pi * Real.exp (837 / 800 : ℝ)) := by
    rw [show (209 / 800 : ℝ) - Real.pi * Real.exp (837 / 800 : ℝ) =
      -(Real.pi * Real.exp (837 / 800 : ℝ) - (209 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (209 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (209 / 200 : ℝ)) := by
    have h := hpThetaJensenCell836_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (29500479423993 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell836_endpointUpper :
    hpThetaJensenKernelEndpointUpper (209 / 400 : ℝ) (837 / 1600 : ℝ) ≤ (228895803 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (837 / 800 : ℝ)) (89439738814079199 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (837 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell836_product_upper
  have hD : (7290876897889 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (209 / 200 : ℝ) - (837 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell836_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell836_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (209 / 200 : ℝ) - (837 / 3200 : ℝ)) ≤
      (1 / (7290876897889 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (7290876897889 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((837 / 3200 : ℝ) - Real.pi * Real.exp (209 / 200 : ℝ)) ≤
      (2 / (7290876897889 / 1250000000 : ℝ) : ℝ) := by
    rw [show (837 / 3200 : ℝ) - Real.pi * Real.exp (209 / 200 : ℝ) =
      -(Real.pi * Real.exp (209 / 200 : ℝ) - (837 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (89439738814079199 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (89439738814079199 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell836_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (209 / 400 : ℝ) (837 / 1600 : ℝ)) :
    (90026583 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (228895803 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell836_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell836_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell837_leftExp :
    (28469549941 / 10000000000 : ℝ) ≤ Real.exp (837 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (837 / 800 : ℝ) (1033235677281 / 1000000000000 : ℝ)
    (28469549941 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell837_rightExp :
    Real.exp (419 / 400 : ℝ) ≤ (28505159131 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (419 / 400 : ℝ) (1033276038839 / 1000000000000 : ℝ)
    (28505159131 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell837_denomUpper :
    Real.exp (86935983389835683 / 10000000000000000 : ℝ) ≤ (59646063496637 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (86935983389835683 / 10000000000000000 : ℝ) (65608020587
    / 50000000000 : ℝ) (59646063496637 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell837_denomLower :
    (58963926862751 / 10000000000 : ℝ) ≤ Real.exp (10852620042280759 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10852620042280759 / 1250000000000000 : ℝ) (327922211081
    / 250000000000 : ℝ) (58963926862751 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell837_product_lower :
    (11179963792280759 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (837 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell837_leftExp
    (by norm_num : (0 : ℝ) ≤ (28469549941 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell837_product_upper :
    Real.pi * Real.exp (419 / 400 : ℝ) ≤ (89551608389835683 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell837_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell837_endpointLower :
    (892983139 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (837 / 1600 : ℝ) (419 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11179963792280759 / 1250000000000000 : ℝ) (Real.pi * Real.exp (837 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell837_product_lower
  have hD : Real.exp (Real.pi * Real.exp (419 / 400 : ℝ) - (837 / 3200 : ℝ)) ≤
      (59646063496637 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell837_denomUpper
    linarith [hpThetaJensenCell837_product_upper]
  have hi : (1 / (59646063496637 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (419 / 400 : ℝ) - (837 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (59646063496637 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (59646063496637 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((837 / 3200 : ℝ) - Real.pi * Real.exp (419 / 400 : ℝ)) := by
    rw [show (837 / 3200 : ℝ) - Real.pi * Real.exp (419 / 400 : ℝ) =
      -(Real.pi * Real.exp (419 / 400 : ℝ) - (837 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (837 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (837 / 800 : ℝ)) := by
    have h := hpThetaJensenCell837_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (59646063496637 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell837_endpointUpper :
    hpThetaJensenKernelEndpointUpper (837 / 1600 : ℝ) (419 / 800 : ℝ) ≤ (908188963 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (419 / 400 : ℝ)) (89551608389835683 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (419 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell837_product_upper
  have hD : (58963926862751 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (837 / 800 : ℝ) - (419 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell837_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell837_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (837 / 800 : ℝ) - (419 / 1600 : ℝ)) ≤
      (1 / (58963926862751 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (58963926862751 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((419 / 1600 : ℝ) - Real.pi * Real.exp (837 / 800 : ℝ)) ≤
      (2 / (58963926862751 / 10000000000 : ℝ) : ℝ) := by
    rw [show (419 / 1600 : ℝ) - Real.pi * Real.exp (837 / 800 : ℝ) =
      -(Real.pi * Real.exp (837 / 800 : ℝ) - (419 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (89551608389835683 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (89551608389835683 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell837_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (837 / 1600 : ℝ) (419 / 800 : ℝ)) :
    (892983139 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (908188963 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell837_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell837_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell838_leftExp :
    (28505159129 / 10000000000 : ℝ) ≤ Real.exp (419 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (419 / 400 : ℝ) (516638019419 / 500000000000 : ℝ)
    (28505159129 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell838_rightExp :
    Real.exp (839 / 800 : ℝ) ≤ (28540812859 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (839 / 800 : ℝ) (258329100493 / 250000000000 : ℝ)
    (28540812859 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell838_denomUpper :
    Real.exp (87044867892144387 / 10000000000000000 : ℝ) ≤ (12059813065533 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (87044867892144387 / 10000000000000000 : ℝ)
    (1312606968751 / 1000000000000 : ℝ) (12059813065533 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell838_denomLower :
    (29804313199601 / 5000000000 : ℝ) ≤ Real.exp (10866213109799171 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10866213109799171 / 1250000000000000 : ℝ) (1312134666947
    / 1000000000000 : ℝ) (29804313199601 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell838_product_lower :
    (11193947484799171 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (419 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell838_leftExp
    (by norm_num : (0 : ℝ) ≤ (28505159129 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell838_product_upper :
    Real.pi * Real.exp (839 / 800 : ℝ) ≤ (89663617892144387 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell838_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell838_endpointLower :
    (110718329 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (419 / 800 : ℝ) (839 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11193947484799171 / 1250000000000000 : ℝ) (Real.pi * Real.exp (419 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell838_product_lower
  have hD : Real.exp (Real.pi * Real.exp (839 / 800 : ℝ) - (419 / 1600 : ℝ)) ≤
      (12059813065533 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell838_denomUpper
    linarith [hpThetaJensenCell838_product_upper]
  have hi : (1 / (12059813065533 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (839 / 800 : ℝ) - (419 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (12059813065533 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (12059813065533 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((419 / 1600 : ℝ) - Real.pi * Real.exp (839 / 800 : ℝ)) := by
    rw [show (419 / 1600 : ℝ) - Real.pi * Real.exp (839 / 800 : ℝ) =
      -(Real.pi * Real.exp (839 / 800 : ℝ) - (419 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (419 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (419 / 400 : ℝ)) := by
    have h := hpThetaJensenCell838_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (12059813065533 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell838_endpointUpper :
    hpThetaJensenKernelEndpointUpper (419 / 800 : ℝ) (839 / 1600 : ℝ) ≤ (1801683 / 20000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (839 / 800 : ℝ)) (89663617892144387 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (839 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell838_product_upper
  have hD : (29804313199601 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (419 / 400 : ℝ) - (839 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell838_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell838_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (419 / 400 : ℝ) - (839 / 3200 : ℝ)) ≤
      (1 / (29804313199601 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (29804313199601 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((839 / 3200 : ℝ) - Real.pi * Real.exp (419 / 400 : ℝ)) ≤
      (2 / (29804313199601 / 5000000000 : ℝ) : ℝ) := by
    rw [show (839 / 3200 : ℝ) - Real.pi * Real.exp (419 / 400 : ℝ) =
      -(Real.pi * Real.exp (419 / 400 : ℝ) - (839 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (89663617892144387 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (89663617892144387 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell838_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (419 / 800 : ℝ) (839 / 1600 : ℝ)) :
    (110718329 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1801683 / 20000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell838_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell838_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell839_leftExp :
    (28540812857 / 10000000000 : ℝ) ≤ Real.exp (839 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (839 / 800 : ℝ) (1033316401971 / 1000000000000 : ℝ)
    (28540812857 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell839_rightExp :
    Real.exp (21 / 20 : ℝ) ≤ (28576511181 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21 / 20 : ℝ) (516678383341 / 500000000000 : ℝ)
    (28576511181 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell839_denomUpper :
    Real.exp (87153892490651333 / 10000000000000000 : ℝ) ≤ (30480035104171 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (87153892490651333 / 10000000000000000 : ℝ)
    (1313054252591 / 1000000000000 : ℝ) (30480035104171 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell839_denomLower :
    (3013060907787 / 500000000 : ℝ) ≤ Real.exp (10879823668131043 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10879823668131043 / 1250000000000000 : ℝ) (26251624301 /
    20000000000 : ℝ) (3013060907787 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell839_product_lower :
    (11207948668131043 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (839 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell839_leftExp
    (by norm_num : (0 : ℝ) ≤ (28540812857 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell839_product_upper :
    Real.pi * Real.exp (21 / 20 : ℝ) ≤ (89775767490651333 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell839_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell839_endpointLower :
    (878556129 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (839 / 1600 : ℝ) (21 / 40 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11207948668131043 / 1250000000000000 : ℝ) (Real.pi * Real.exp (839 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell839_product_lower
  have hD : Real.exp (Real.pi * Real.exp (21 / 20 : ℝ) - (839 / 3200 : ℝ)) ≤
      (30480035104171 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell839_denomUpper
    linarith [hpThetaJensenCell839_product_upper]
  have hi : (1 / (30480035104171 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (21 / 20 : ℝ) - (839 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (30480035104171 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (30480035104171 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((839 / 3200 : ℝ) - Real.pi * Real.exp (21 / 20 : ℝ)) := by
    rw [show (839 / 3200 : ℝ) - Real.pi * Real.exp (21 / 20 : ℝ) =
      -(Real.pi * Real.exp (21 / 20 : ℝ) - (839 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (839 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (839 / 800 : ℝ)) := by
    have h := hpThetaJensenCell839_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (30480035104171 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell839_endpointUpper :
    hpThetaJensenKernelEndpointUpper (839 / 1600 : ℝ) (21 / 40 : ℝ) ≤ (5584629 / 62500000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (21 / 20 : ℝ)) (89775767490651333 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (21 / 40 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell839_product_upper
  have hD : (3013060907787 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (839 / 800 : ℝ) - (21 / 80 : ℝ)) := by
    apply le_trans hpThetaJensenCell839_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell839_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (839 / 800 : ℝ) - (21 / 80 : ℝ)) ≤
      (1 / (3013060907787 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3013060907787 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((21 / 80 : ℝ) - Real.pi * Real.exp (839 / 800 : ℝ)) ≤
      (2 / (3013060907787 / 500000000 : ℝ) : ℝ) := by
    rw [show (21 / 80 : ℝ) - Real.pi * Real.exp (839 / 800 : ℝ) =
      -(Real.pi * Real.exp (839 / 800 : ℝ) - (21 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (89775767490651333 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (89775767490651333 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell839_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (839 / 1600 : ℝ) (21 / 40 : ℝ)) :
    (878556129 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5584629 / 62500000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell839_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell839_endpointUpper

def hpThetaJensenCellsBatch041Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (204643531 / 2000000000 : ℝ)
  | 1 => (203034287 / 2000000000 : ℝ)
  | 2 => (503587141 / 5000000000 : ℝ)
  | 3 => (499613009 / 5000000000 : ℝ)
  | 4 => (991326463 / 10000000000 : ℝ)
  | 5 => (12293443 / 125000000 : ℝ)
  | 6 => (15244887 / 156250000 : ℝ)
  | 7 => (967918269 / 10000000000 : ℝ)
  | 8 => (240052941 / 2500000000 : ℝ)
  | 9 => (952553071 / 10000000000 : ℝ)
  | 10 => (944942011 / 10000000000 : ℝ)
  | 11 => (234344601 / 2500000000 : ℝ)
  | 12 => (929862069 / 10000000000 : ℝ)
  | 13 => (36895713 / 400000000 : ℝ)
  | 14 => (228742623 / 2500000000 : ℝ)
  | 15 => (907594887 / 10000000000 : ℝ)
  | 16 => (90026583 / 1000000000 : ℝ)
  | 17 => (892983139 / 10000000000 : ℝ)
  | 18 => (110718329 / 1250000000 : ℝ)
  | 19 => (878556129 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch041Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (260100777 / 2500000000 : ℝ)
  | 1 => (1032235489 / 10000000000 : ℝ)
  | 2 => (1024117563 / 10000000000 : ℝ)
  | 3 => (1016049151 / 10000000000 : ℝ)
  | 4 => (1008030071 / 10000000000 : ℝ)
  | 5 => (62503759 / 625000000 : ℝ)
  | 6 => (99213919 / 1000000000 : ℝ)
  | 7 => (984267027 / 10000000000 : ℝ)
  | 8 => (39057739 / 400000000 : ℝ)
  | 9 => (968668351 / 10000000000 : ℝ)
  | 10 => (38437659 / 400000000 : ℝ)
  | 11 => (119157833 / 1250000000 : ℝ)
  | 12 => (945631737 / 10000000000 : ℝ)
  | 13 => (938048511 / 10000000000 : ℝ)
  | 14 => (930512803 / 10000000000 : ℝ)
  | 15 => (923024431 / 10000000000 : ℝ)
  | 16 => (228895803 / 2500000000 : ℝ)
  | 17 => (908188963 / 10000000000 : ℝ)
  | 18 => (1801683 / 20000000 : ℝ)
  | 19 => (5584629 / 62500000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch041_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((820 : ℝ) + (j.val : ℝ)) / 1600)
      (((820 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch041Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch041Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell820_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell821_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell822_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell823_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell824_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell825_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell826_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell827_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell828_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell829_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell830_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell831_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell832_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell833_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell834_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell835_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell836_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell837_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell838_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell839_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper] at h ⊢
    exact h

end HodgeProofHP
