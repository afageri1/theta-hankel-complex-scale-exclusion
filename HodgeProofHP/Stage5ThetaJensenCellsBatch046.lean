import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell920_leftExp :
    (3947741137 / 1250000000 : ℝ) ≤ Real.exp (23 / 20 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (23 / 20 : ℝ) (41463642301 / 40000000000 : ℝ) (3947741137
    / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell920_rightExp :
    Real.exp (921 / 800 : ℝ) ≤ (31621431193 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (921 / 800 : ℝ) (207326310031 / 200000000000 : ℝ)
    (31621431193 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell920_denomUpper :
    Real.exp (96466666885910449 / 10000000000000000 : ℝ) ≤ (154701352863591 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (96466666885910449 / 10000000000000000 : ℝ) (337957197173
    / 250000000000 : ℝ) (154701352863591 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell920_denomLower :
    (152745157170427 / 10000000000 : ℝ) ≤ Real.exp (1505303293633763 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1505303293633763 / 156250000000000 : ℝ) (675645653331 /
    500000000000 : ℝ) (152745157170427 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell920_product_lower :
    (1550273996758763 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (23 / 20 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell920_leftExp
    (by norm_num : (0 : ℝ) ≤ (3947741137 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell920_product_upper :
    Real.pi * Real.exp (921 / 800 : ℝ) ≤ (99341666885910449 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell920_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell920_endpointLower :
    (216051281 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (23 / 40 : ℝ) (921 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1550273996758763 / 156250000000000 : ℝ) (Real.pi * Real.exp (23 / 20 : ℝ))
    (by norm_num) hpThetaJensenCell920_product_lower
  have hD : Real.exp (Real.pi * Real.exp (921 / 800 : ℝ) - (23 / 80 : ℝ)) ≤
      (154701352863591 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell920_denomUpper
    linarith [hpThetaJensenCell920_product_upper]
  have hi : (1 / (154701352863591 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (921 / 800 : ℝ) - (23 / 80 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (154701352863591 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (154701352863591 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((23 / 80 : ℝ) - Real.pi * Real.exp (921 / 800 : ℝ)) := by
    rw [show (23 / 80 : ℝ) - Real.pi * Real.exp (921 / 800 : ℝ) =
      -(Real.pi * Real.exp (921 / 800 : ℝ) - (23 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (23 / 20 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (23 / 20 : ℝ)) := by
    have h := hpThetaJensenCell920_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (154701352863591 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell920_endpointUpper :
    hpThetaJensenKernelEndpointUpper (23 / 40 : ℝ) (921 / 1600 : ℝ) ≤ (5499819 / 125000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (921 / 800 : ℝ)) (99341666885910449 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (921 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell920_product_upper
  have hD : (152745157170427 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (23 / 20 : ℝ) - (921 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell920_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell920_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (23 / 20 : ℝ) - (921 / 3200 : ℝ)) ≤
      (1 / (152745157170427 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (152745157170427 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((921 / 3200 : ℝ) - Real.pi * Real.exp (23 / 20 : ℝ)) ≤
      (2 / (152745157170427 / 10000000000 : ℝ) : ℝ) := by
    rw [show (921 / 3200 : ℝ) - Real.pi * Real.exp (23 / 20 : ℝ) =
      -(Real.pi * Real.exp (23 / 20 : ℝ) - (921 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (99341666885910449 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (99341666885910449 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell920_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (23 / 40 : ℝ) (921 / 1600 : ℝ)) :
    (216051281 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5499819 / 125000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell920_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell920_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell921_leftExp :
    (31621431191 / 10000000000 : ℝ) ≤ Real.exp (921 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (921 / 800 : ℝ) (518315775077 / 500000000000 : ℝ)
    (31621431191 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell921_rightExp :
    Real.exp (461 / 400 : ℝ) ≤ (31660982697 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (461 / 400 : ℝ) (518336022183 / 500000000000 : ℝ)
    (31660982697 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell921_denomUpper :
    Real.exp (96587796614016321 / 10000000000000000 : ℝ) ≤ (2446666270559 / 156250000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (96587796614016321 / 10000000000000000 : ℝ) (270468118769
    / 200000000000 : ℝ) (2446666270559 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell921_denomLower :
    (154604205743733 / 10000000000 : ℝ) ≤ Real.exp (12057548157274509 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (12057548157274509 / 1250000000000000 : ℝ) (270360450487
    / 200000000000 : ℝ) (154604205743733 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell921_product_lower :
    (12417704407274509 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (921 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell921_leftExp
    (by norm_num : (0 : ℝ) ≤ (31621431191 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell921_product_upper :
    Real.pi * Real.exp (461 / 400 : ℝ) ≤ (99465921614016321 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell921_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell921_endpointLower :
    (85612779 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (921 / 1600 : ℝ) (461 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12417704407274509 / 1250000000000000 : ℝ) (Real.pi * Real.exp (921 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell921_product_lower
  have hD : Real.exp (Real.pi * Real.exp (461 / 400 : ℝ) - (921 / 3200 : ℝ)) ≤
      (2446666270559 / 156250000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell921_denomUpper
    linarith [hpThetaJensenCell921_product_upper]
  have hi : (1 / (2446666270559 / 156250000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (461 / 400 : ℝ) - (921 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2446666270559 / 156250000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2446666270559 / 156250000 : ℝ) : ℝ) ≤
      2 * Real.exp ((921 / 3200 : ℝ) - Real.pi * Real.exp (461 / 400 : ℝ)) := by
    rw [show (921 / 3200 : ℝ) - Real.pi * Real.exp (461 / 400 : ℝ) =
      -(Real.pi * Real.exp (461 / 400 : ℝ) - (921 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (921 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (921 / 800 : ℝ)) := by
    have h := hpThetaJensenCell921_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2446666270559 / 156250000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell921_endpointUpper :
    hpThetaJensenKernelEndpointUpper (921 / 1600 : ℝ) (461 / 800 : ℝ) ≤ (2179399 / 50000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (461 / 400 : ℝ)) (99465921614016321 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (461 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell921_product_upper
  have hD : (154604205743733 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (921 / 800 : ℝ) - (461 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell921_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell921_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (921 / 800 : ℝ) - (461 / 1600 : ℝ)) ≤
      (1 / (154604205743733 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (154604205743733 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((461 / 1600 : ℝ) - Real.pi * Real.exp (921 / 800 : ℝ)) ≤
      (2 / (154604205743733 / 10000000000 : ℝ) : ℝ) := by
    rw [show (461 / 1600 : ℝ) - Real.pi * Real.exp (921 / 800 : ℝ) =
      -(Real.pi * Real.exp (921 / 800 : ℝ) - (461 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (99465921614016321 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (99465921614016321 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell921_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (921 / 1600 : ℝ) (461 / 800 : ℝ)) :
    (85612779 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2179399 / 50000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell921_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell921_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell922_leftExp :
    (6332196539 / 2000000000 : ℝ) ≤ Real.exp (461 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (461 / 400 : ℝ) (207334408873 / 200000000000 : ℝ)
    (6332196539 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell922_rightExp :
    Real.exp (923 / 800 : ℝ) ≤ (3170058367 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (923 / 800 : ℝ) (518356270079 / 500000000000 : ℝ)
    (3170058367 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell922_denomUpper :
    Real.exp (9670908175358631 / 1000000000000000 : ℝ) ≤ (79248684149671 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9670908175358631 / 1000000000000000 : ℝ) (1352853249797
    / 1000000000000 : ℝ) (79248684149671 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell922_denomLower :
    (78244154841921 / 5000000000 : ℝ) ≤ Real.exp (2414537873668761 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2414537873668761 / 250000000000000 : ℝ) (10818512379 /
    8000000000 : ℝ) (78244154841921 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell922_product_lower :
    (2486647248668761 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (461 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell922_leftExp
    (by norm_num : (0 : ℝ) ≤ (6332196539 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell922_product_upper :
    Real.pi * Real.exp (923 / 800 : ℝ) ≤ (9959033175358631 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell922_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell922_endpointLower :
    (424056247 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (461 / 800 : ℝ) (923 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2486647248668761 / 250000000000000 : ℝ) (Real.pi * Real.exp (461 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell922_product_lower
  have hD : Real.exp (Real.pi * Real.exp (923 / 800 : ℝ) - (461 / 1600 : ℝ)) ≤
      (79248684149671 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell922_denomUpper
    linarith [hpThetaJensenCell922_product_upper]
  have hi : (1 / (79248684149671 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (923 / 800 : ℝ) - (461 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (79248684149671 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (79248684149671 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((461 / 1600 : ℝ) - Real.pi * Real.exp (923 / 800 : ℝ)) := by
    rw [show (461 / 1600 : ℝ) - Real.pi * Real.exp (923 / 800 : ℝ) =
      -(Real.pi * Real.exp (923 / 800 : ℝ) - (461 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (461 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (461 / 400 : ℝ)) := by
    have h := hpThetaJensenCell922_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (79248684149671 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell922_endpointUpper :
    hpThetaJensenKernelEndpointUpper (461 / 800 : ℝ) (923 / 1600 : ℝ) ≤ (431805549 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (923 / 800 : ℝ)) (9959033175358631 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (923 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell922_product_upper
  have hD : (78244154841921 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (461 / 400 : ℝ) - (923 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell922_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell922_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (461 / 400 : ℝ) - (923 / 3200 : ℝ)) ≤
      (1 / (78244154841921 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (78244154841921 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((923 / 3200 : ℝ) - Real.pi * Real.exp (461 / 400 : ℝ)) ≤
      (2 / (78244154841921 / 5000000000 : ℝ) : ℝ) := by
    rw [show (923 / 3200 : ℝ) - Real.pi * Real.exp (461 / 400 : ℝ) =
      -(Real.pi * Real.exp (461 / 400 : ℝ) - (923 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9959033175358631 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (9959033175358631 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell922_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (461 / 800 : ℝ) (923 / 1600 : ℝ)) :
    (424056247 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (431805549 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell922_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell922_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell923_leftExp :
    (7925145917 / 2500000000 : ℝ) ≤ Real.exp (923 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (923 / 800 : ℝ) (1036712540157 / 1000000000000 : ℝ)
    (7925145917 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell923_rightExp :
    Real.exp (231 / 200 : ℝ) ≤ (495941159 / 156250000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (231 / 200 : ℝ) (1036753037533 / 1000000000000 : ℝ)
    (495941159 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell923_denomUpper :
    Real.exp (1512976914151287 / 156250000000000 : ℝ) ≤ (40108476798891 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1512976914151287 / 156250000000000 : ℝ) (1353366758217 /
    1000000000000 : ℝ) (40108476798891 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell923_denomLower :
    (3959945903941 / 250000000 : ℝ) ≤ Real.exp (3021962501459983 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3021962501459983 / 312500000000000 : ℝ) (270565338619 /
    200000000000 : ℝ) (3959945903941 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell923_product_lower :
    (3112196876459983 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (923 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell923_leftExp
    (by norm_num : (0 : ℝ) ≤ (7925145917 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell923_product_upper :
    Real.pi * Real.exp (231 / 200 : ℝ) ≤ (1558045273526287 / 156250000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell923_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell923_endpointLower :
    (210039723 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (923 / 1600 : ℝ) (231 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3112196876459983 / 312500000000000 : ℝ) (Real.pi * Real.exp (923 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell923_product_lower
  have hD : Real.exp (Real.pi * Real.exp (231 / 200 : ℝ) - (923 / 3200 : ℝ)) ≤
      (40108476798891 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell923_denomUpper
    linarith [hpThetaJensenCell923_product_upper]
  have hi : (1 / (40108476798891 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (231 / 200 : ℝ) - (923 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (40108476798891 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (40108476798891 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((923 / 3200 : ℝ) - Real.pi * Real.exp (231 / 200 : ℝ)) := by
    rw [show (923 / 3200 : ℝ) - Real.pi * Real.exp (231 / 200 : ℝ) =
      -(Real.pi * Real.exp (231 / 200 : ℝ) - (923 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (923 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (923 / 800 : ℝ)) := by
    have h := hpThetaJensenCell923_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (40108476798891 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell923_endpointUpper :
    hpThetaJensenKernelEndpointUpper (923 / 1600 : ℝ) (231 / 400 : ℝ) ≤ (427762593 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (231 / 200 : ℝ)) (1558045273526287 / 156250000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (231 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell923_product_upper
  have hD : (3959945903941 / 250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (923 / 800 : ℝ) - (231 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell923_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell923_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (923 / 800 : ℝ) - (231 / 800 : ℝ)) ≤
      (1 / (3959945903941 / 250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3959945903941 / 250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((231 / 800 : ℝ) - Real.pi * Real.exp (923 / 800 : ℝ)) ≤
      (2 / (3959945903941 / 250000000 : ℝ) : ℝ) := by
    rw [show (231 / 800 : ℝ) - Real.pi * Real.exp (923 / 800 : ℝ) =
      -(Real.pi * Real.exp (923 / 800 : ℝ) - (231 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1558045273526287 / 156250000000000 : ℝ) ^ 2 - 6 *
      (1558045273526287 / 156250000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell923_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (923 / 1600 : ℝ) (231 / 400 : ℝ)) :
    (210039723 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (427762593 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell923_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell923_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell924_leftExp :
    (15870117087 / 5000000000 : ℝ) ≤ Real.exp (231 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (231 / 200 : ℝ) (259188259383 / 250000000000 : ℝ)
    (15870117087 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell924_rightExp :
    Real.exp (37 / 32 : ℝ) ≤ (7944983569 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (37 / 32 : ℝ) (1036793536489 / 1000000000000 : ℝ)
    (7944983569 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell924_denomUpper :
    Real.exp (24238029765485417 / 2500000000000000 : ℝ) ≤ (162396637136061 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (24238029765485417 / 2500000000000000 : ℝ) (1353881120741
    / 1000000000000 : ℝ) (162396637136061 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell924_denomLower :
    (160333158326627 / 10000000000 : ℝ) ≤ Real.exp (6051515047447813 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6051515047447813 / 625000000000000 : ℝ) (338335047817 /
    250000000000 : ℝ) (160333158326627 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell924_product_lower :
    (6232179109947813 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (231 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell924_leftExp
    (by norm_num : (0 : ℝ) ≤ (15870117087 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell924_product_upper :
    Real.pi * Real.exp (37 / 32 : ℝ) ≤ (24959904765485417 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell924_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell924_endpointLower :
    (416133319 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (231 / 400 : ℝ) (37 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6232179109947813 / 625000000000000 : ℝ) (Real.pi * Real.exp (231 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell924_product_lower
  have hD : Real.exp (Real.pi * Real.exp (37 / 32 : ℝ) - (231 / 800 : ℝ)) ≤
      (162396637136061 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell924_denomUpper
    linarith [hpThetaJensenCell924_product_upper]
  have hi : (1 / (162396637136061 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (37 / 32 : ℝ) - (231 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (162396637136061 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (162396637136061 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((231 / 800 : ℝ) - Real.pi * Real.exp (37 / 32 : ℝ)) := by
    rw [show (231 / 800 : ℝ) - Real.pi * Real.exp (37 / 32 : ℝ) =
      -(Real.pi * Real.exp (37 / 32 : ℝ) - (231 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (231 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (231 / 200 : ℝ)) := by
    have h := hpThetaJensenCell924_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (162396637136061 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell924_endpointUpper :
    hpThetaJensenKernelEndpointUpper (231 / 400 : ℝ) (37 / 64 : ℝ) ≤ (211875379 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (37 / 32 : ℝ)) (24959904765485417 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (37 / 64 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell924_product_upper
  have hD : (160333158326627 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (231 / 200 : ℝ) - (37 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell924_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell924_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (231 / 200 : ℝ) - (37 / 128 : ℝ)) ≤
      (1 / (160333158326627 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (160333158326627 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((37 / 128 : ℝ) - Real.pi * Real.exp (231 / 200 : ℝ)) ≤
      (2 / (160333158326627 / 10000000000 : ℝ) : ℝ) := by
    rw [show (37 / 128 : ℝ) - Real.pi * Real.exp (231 / 200 : ℝ) =
      -(Real.pi * Real.exp (231 / 200 : ℝ) - (37 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (24959904765485417 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (24959904765485417 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell924_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (231 / 400 : ℝ) (37 / 64 : ℝ)) :
    (416133319 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (211875379 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell924_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell924_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell925_leftExp :
    (15889967137 / 5000000000 : ℝ) ≤ Real.exp (37 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (37 / 32 : ℝ) (129599192061 / 125000000000 : ℝ)
    (15889967137 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell925_rightExp :
    Real.exp (463 / 400 : ℝ) ≤ (31819684033 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (463 / 400 : ℝ) (259208509257 / 250000000000 : ℝ)
    (31819684033 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell925_denomUpper :
    Real.exp (97073871620284569 / 10000000000000000 : ℝ) ≤ (164385943322611 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (97073871620284569 / 10000000000000000 : ℝ)
    (1354396339031 / 1000000000000 : ℝ) (164385943322611 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell925_denomLower :
    (162294655069057 / 10000000000 : ℝ) ≤ Real.exp (6059114829732763 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6059114829732763 / 625000000000000 : ℝ) (676927271763 /
    500000000000 : ℝ) (162294655069057 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell925_product_lower :
    (6239974204732763 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (37 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell925_leftExp
    (by norm_num : (0 : ℝ) ≤ (15889967137 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell925_product_upper :
    Real.pi * Real.exp (463 / 400 : ℝ) ≤ (99964496620284569 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell925_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell925_endpointLower :
    (412217697 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (37 / 64 : ℝ) (463 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6239974204732763 / 625000000000000 : ℝ) (Real.pi * Real.exp (37 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell925_product_lower
  have hD : Real.exp (Real.pi * Real.exp (463 / 400 : ℝ) - (37 / 128 : ℝ)) ≤
      (164385943322611 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell925_denomUpper
    linarith [hpThetaJensenCell925_product_upper]
  have hi : (1 / (164385943322611 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (463 / 400 : ℝ) - (37 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (164385943322611 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (164385943322611 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((37 / 128 : ℝ) - Real.pi * Real.exp (463 / 400 : ℝ)) := by
    rw [show (37 / 128 : ℝ) - Real.pi * Real.exp (463 / 400 : ℝ) =
      -(Real.pi * Real.exp (463 / 400 : ℝ) - (37 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (37 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (37 / 32 : ℝ)) := by
    have h := hpThetaJensenCell925_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (164385943322611 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell925_endpointUpper :
    hpThetaJensenKernelEndpointUpper (37 / 64 : ℝ) (463 / 800 : ℝ) ≤ (419769873 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (463 / 400 : ℝ)) (99964496620284569 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (463 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell925_product_upper
  have hD : (162294655069057 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (37 / 32 : ℝ) - (463 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell925_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell925_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (37 / 32 : ℝ) - (463 / 1600 : ℝ)) ≤
      (1 / (162294655069057 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (162294655069057 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((463 / 1600 : ℝ) - Real.pi * Real.exp (37 / 32 : ℝ)) ≤
      (2 / (162294655069057 / 10000000000 : ℝ) : ℝ) := by
    rw [show (463 / 1600 : ℝ) - Real.pi * Real.exp (37 / 32 : ℝ) =
      -(Real.pi * Real.exp (37 / 32 : ℝ) - (463 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (99964496620284569 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (99964496620284569 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell925_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (37 / 64 : ℝ) (463 / 800 : ℝ)) :
    (412217697 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (419769873 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell925_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell925_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell926_leftExp :
    (31819684031 / 10000000000 : ℝ) ≤ Real.exp (463 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (463 / 400 : ℝ) (1036834037027 / 1000000000000 : ℝ)
    (31819684031 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell926_rightExp :
    Real.exp (927 / 800 : ℝ) ≤ (31859483507 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (927 / 800 : ℝ) (259218634787 / 250000000000 : ℝ)
    (31859483507 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell926_denomUpper :
    Real.exp (97195780369206651 / 10000000000000000 : ℝ) ≤ (83201108444599 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (97195780369206651 / 10000000000000000 : ℝ)
    (1354912414713 / 1000000000000 : ℝ) (83201108444599 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell926_denomLower :
    (164282711355983 / 10000000000 : ℝ) ≤ Real.exp (12133448724289669 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (12133448724289669 / 1250000000000000 : ℝ) (677184875767
    / 500000000000 : ℝ) (164282711355983 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell926_product_lower :
    (12495558099289669 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (463 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell926_leftExp
    (by norm_num : (0 : ℝ) ≤ (31819684031 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell926_product_upper :
    Real.pi * Real.exp (927 / 800 : ℝ) ≤ (100089530369206651 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell926_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell926_endpointLower :
    (51041551 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (463 / 800 : ℝ) (927 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12495558099289669 / 1250000000000000 : ℝ) (Real.pi * Real.exp (463 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell926_product_lower
  have hD : Real.exp (Real.pi * Real.exp (927 / 800 : ℝ) - (463 / 1600 : ℝ)) ≤
      (83201108444599 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell926_denomUpper
    linarith [hpThetaJensenCell926_product_upper]
  have hi : (1 / (83201108444599 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (927 / 800 : ℝ) - (463 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (83201108444599 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (83201108444599 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((463 / 1600 : ℝ) - Real.pi * Real.exp (927 / 800 : ℝ)) := by
    rw [show (463 / 1600 : ℝ) - Real.pi * Real.exp (927 / 800 : ℝ) =
      -(Real.pi * Real.exp (927 / 800 : ℝ) - (463 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (463 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (463 / 400 : ℝ)) := by
    have h := hpThetaJensenCell926_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (83201108444599 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell926_endpointUpper :
    hpThetaJensenKernelEndpointUpper (463 / 800 : ℝ) (927 / 1600 : ℝ) ≤ (103954941 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (927 / 800 : ℝ)) (100089530369206651 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (927 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell926_product_upper
  have hD : (164282711355983 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (463 / 400 : ℝ) - (927 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell926_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell926_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (463 / 400 : ℝ) - (927 / 3200 : ℝ)) ≤
      (1 / (164282711355983 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (164282711355983 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((927 / 3200 : ℝ) - Real.pi * Real.exp (463 / 400 : ℝ)) ≤
      (2 / (164282711355983 / 10000000000 : ℝ) : ℝ) := by
    rw [show (927 / 3200 : ℝ) - Real.pi * Real.exp (463 / 400 : ℝ) =
      -(Real.pi * Real.exp (463 / 400 : ℝ) - (927 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (100089530369206651 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (100089530369206651 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell926_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (463 / 800 : ℝ) (927 / 1600 : ℝ)) :
    (51041551 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (103954941 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell926_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell926_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell927_leftExp :
    (6371896701 / 2000000000 : ℝ) ≤ Real.exp (927 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (927 / 800 : ℝ) (1036874539147 / 1000000000000 : ℝ)
    (6371896701 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell927_rightExp :
    Real.exp (29 / 25 : ℝ) ≤ (15949666381 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (29 / 25 : ℝ) (1036915042851 / 1000000000000 : ℝ)
    (15949666381 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell927_denomUpper :
    Real.exp (48658922754884933 / 5000000000000000 : ℝ) ≤ (84222927682527 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (48658922754884933 / 5000000000000000 : ℝ) (135542934947
    / 100000000000 : ℝ) (84222927682527 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell927_denomLower :
    (166297718071769 / 10000000000 : ℝ) ≤ Real.exp (2429737462585999 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2429737462585999 / 250000000000000 : ℝ) (1354885816917 /
    1000000000000 : ℝ) (166297718071769 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell927_product_lower :
    (2502237462585999 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (927 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell927_leftExp
    (by norm_num : (0 : ℝ) ≤ (6371896701 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell927_product_upper :
    Real.pi * Real.exp (29 / 25 : ℝ) ≤ (50107360254884933 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell927_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell927_endpointLower :
    (202238641 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (927 / 1600 : ℝ) (29 / 50 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2502237462585999 / 250000000000000 : ℝ) (Real.pi * Real.exp (927 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell927_product_lower
  have hD : Real.exp (Real.pi * Real.exp (29 / 25 : ℝ) - (927 / 3200 : ℝ)) ≤
      (84222927682527 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell927_denomUpper
    linarith [hpThetaJensenCell927_product_upper]
  have hi : (1 / (84222927682527 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (29 / 25 : ℝ) - (927 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (84222927682527 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (84222927682527 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((927 / 3200 : ℝ) - Real.pi * Real.exp (29 / 25 : ℝ)) := by
    rw [show (927 / 3200 : ℝ) - Real.pi * Real.exp (29 / 25 : ℝ) =
      -(Real.pi * Real.exp (29 / 25 : ℝ) - (927 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (927 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (927 / 800 : ℝ)) := by
    have h := hpThetaJensenCell927_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (84222927682527 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell927_endpointUpper :
    hpThetaJensenKernelEndpointUpper (927 / 1600 : ℝ) (29 / 50 : ℝ) ≤ (205950129 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (29 / 25 : ℝ)) (50107360254884933 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (29 / 50 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell927_product_upper
  have hD : (166297718071769 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (927 / 800 : ℝ) - (29 / 100 : ℝ)) := by
    apply le_trans hpThetaJensenCell927_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell927_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (927 / 800 : ℝ) - (29 / 100 : ℝ)) ≤
      (1 / (166297718071769 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (166297718071769 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((29 / 100 : ℝ) - Real.pi * Real.exp (927 / 800 : ℝ)) ≤
      (2 / (166297718071769 / 10000000000 : ℝ) : ℝ) := by
    rw [show (29 / 100 : ℝ) - Real.pi * Real.exp (927 / 800 : ℝ) =
      -(Real.pi * Real.exp (927 / 800 : ℝ) - (29 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (50107360254884933 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (50107360254884933 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell927_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (927 / 1600 : ℝ) (29 / 50 : ℝ)) :
    (202238641 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (205950129 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell927_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell927_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell928_leftExp :
    (797483319 / 250000000 : ℝ) ≤ Real.exp (29 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (29 / 25 : ℝ) (20738300857 / 20000000000 : ℝ) (797483319
    / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell928_rightExp :
    Real.exp (929 / 800 : ℝ) ≤ (1596961593 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (929 / 800 : ℝ) (129619443517 / 125000000000 : ℝ)
    (1596961593 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell928_denomUpper :
    Real.exp (4872003361837649 / 500000000000000 : ℝ) ≤ (170517262461371 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4872003361837649 / 500000000000000 : ℝ) (1059333707 /
    781250000 : ℝ) (170517262461371 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell928_denomLower :
    (168340072491833 / 10000000000 : ℝ) ≤ Real.exp (304098636262981 / 31250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (304098636262981 / 31250000000000 : ℝ) (1355402741357 /
    1000000000000 : ℝ) (168340072491833 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell928_product_lower :
    (313170901887981 / 31250000000000 : ℝ) ≤ Real.pi * Real.exp (29 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell928_leftExp
    (by norm_num : (0 : ℝ) ≤ (797483319 / 250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell928_product_upper :
    Real.pi * Real.exp (929 / 800 : ℝ) ≤ (5017003361837649 / 500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell928_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell928_endpointLower :
    (8013043 / 200000000 : ℝ) ≤ hpThetaTraceEndpointLower (29 / 50 : ℝ) (929 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (313170901887981 / 31250000000000 : ℝ) (Real.pi * Real.exp (29 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell928_product_lower
  have hD : Real.exp (Real.pi * Real.exp (929 / 800 : ℝ) - (29 / 100 : ℝ)) ≤
      (170517262461371 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell928_denomUpper
    linarith [hpThetaJensenCell928_product_upper]
  have hi : (1 / (170517262461371 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (929 / 800 : ℝ) - (29 / 100 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (170517262461371 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (170517262461371 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((29 / 100 : ℝ) - Real.pi * Real.exp (929 / 800 : ℝ)) := by
    rw [show (29 / 100 : ℝ) - Real.pi * Real.exp (929 / 800 : ℝ) =
      -(Real.pi * Real.exp (929 / 800 : ℝ) - (29 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (29 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (29 / 25 : ℝ)) := by
    have h := hpThetaJensenCell928_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (170517262461371 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell928_endpointUpper :
    hpThetaJensenKernelEndpointUpper (29 / 50 : ℝ) (929 / 1600 : ℝ) ≤ (204005593 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (929 / 800 : ℝ)) (5017003361837649 / 500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (929 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell928_product_upper
  have hD : (168340072491833 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (29 / 25 : ℝ) - (929 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell928_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell928_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (29 / 25 : ℝ) - (929 / 3200 : ℝ)) ≤
      (1 / (168340072491833 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (168340072491833 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((929 / 3200 : ℝ) - Real.pi * Real.exp (29 / 25 : ℝ)) ≤
      (2 / (168340072491833 / 10000000000 : ℝ) : ℝ) := by
    rw [show (929 / 3200 : ℝ) - Real.pi * Real.exp (29 / 25 : ℝ) =
      -(Real.pi * Real.exp (29 / 25 : ℝ) - (929 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (5017003361837649 / 500000000000000 : ℝ) ^ 2 - 6 *
      (5017003361837649 / 500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell928_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (29 / 50 : ℝ) (929 / 1600 : ℝ)) :
    (8013043 / 200000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (204005593 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell928_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell928_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell929_leftExp :
    (15969615929 / 5000000000 : ℝ) ≤ Real.exp (929 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (929 / 800 : ℝ) (207391109627 / 200000000000 : ℝ)
    (15969615929 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell929_rightExp :
    Real.exp (93 / 80 : ℝ) ≤ (15989590431 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (93 / 80 : ℝ) (1036996055003 / 1000000000000 : ℝ)
    (15989590431 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell929_denomUpper :
    Real.exp (48781222870896583 / 5000000000000000 : ℝ) ≤ (86308424115871 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (48781222870896583 / 5000000000000000 : ℝ) (1356465802831
    / 1000000000000 : ℝ) (86308424115871 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell929_denomLower :
    (85205089038761 / 5000000000 : ℝ) ≤ Real.exp (6089611580702371 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6089611580702371 / 625000000000000 : ℝ) (1355920526513 /
    1000000000000 : ℝ) (85205089038761 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell929_product_lower :
    (6271252205702371 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (929 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell929_leftExp
    (by norm_num : (0 : ℝ) ≤ (15969615929 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell929_product_upper :
    Real.pi * Real.exp (93 / 80 : ℝ) ≤ (50232785370896583 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell929_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell929_endpointLower :
    (396856841 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (929 / 1600 : ℝ) (93 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6271252205702371 / 625000000000000 : ℝ) (Real.pi * Real.exp (929 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell929_product_lower
  have hD : Real.exp (Real.pi * Real.exp (93 / 80 : ℝ) - (929 / 3200 : ℝ)) ≤
      (86308424115871 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell929_denomUpper
    linarith [hpThetaJensenCell929_product_upper]
  have hi : (1 / (86308424115871 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (93 / 80 : ℝ) - (929 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (86308424115871 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (86308424115871 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((929 / 3200 : ℝ) - Real.pi * Real.exp (93 / 80 : ℝ)) := by
    rw [show (929 / 3200 : ℝ) - Real.pi * Real.exp (93 / 80 : ℝ) =
      -(Real.pi * Real.exp (93 / 80 : ℝ) - (929 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (929 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (929 / 800 : ℝ)) := by
    have h := hpThetaJensenCell929_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (86308424115871 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell929_endpointUpper :
    hpThetaJensenKernelEndpointUpper (929 / 1600 : ℝ) (93 / 160 : ℝ) ≤ (404152373 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (93 / 80 : ℝ)) (50232785370896583 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (93 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell929_product_upper
  have hD : (85205089038761 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (929 / 800 : ℝ) - (93 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell929_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell929_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (929 / 800 : ℝ) - (93 / 320 : ℝ)) ≤
      (1 / (85205089038761 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (85205089038761 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((93 / 320 : ℝ) - Real.pi * Real.exp (929 / 800 : ℝ)) ≤
      (2 / (85205089038761 / 5000000000 : ℝ) : ℝ) := by
    rw [show (93 / 320 : ℝ) - Real.pi * Real.exp (929 / 800 : ℝ) =
      -(Real.pi * Real.exp (929 / 800 : ℝ) - (93 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (50232785370896583 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (50232785370896583 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell929_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (929 / 1600 : ℝ) (93 / 160 : ℝ)) :
    (396856841 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (404152373 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell929_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell929_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell930_leftExp :
    (1598959043 / 500000000 : ℝ) ≤ Real.exp (93 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (93 / 80 : ℝ) (518498027501 / 500000000000 : ℝ)
    (1598959043 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell930_rightExp :
    Real.exp (931 / 800 : ℝ) ≤ (32019179833 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (931 / 800 : ℝ) (1037036563453 / 1000000000000 : ℝ)
    (32019179833 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell930_denomUpper :
    Real.exp (97684981229093969 / 10000000000000000 : ℝ) ≤ (174745029448767 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (97684981229093969 / 10000000000000000 : ℝ)
    (1356985324787 / 1000000000000 : ℝ) (174745029448767 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell930_denomLower :
    (172508444628789 / 10000000000 : ℝ) ≤ Real.exp (609726023477057 / 62500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (609726023477057 / 62500000000000 : ℝ) (678219587017 /
    500000000000 : ℝ) (172508444628789 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell930_product_lower :
    (627909617227057 / 62500000000000 : ℝ) ≤ Real.pi * Real.exp (93 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell930_leftExp
    (by norm_num : (0 : ℝ) ≤ (1598959043 / 500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell930_product_upper :
    Real.pi * Real.exp (931 / 800 : ℝ) ≤ (100591231229093969 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell930_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell930_endpointLower :
    (393091187 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (93 / 160 : ℝ) (931 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (627909617227057 / 62500000000000 : ℝ) (Real.pi * Real.exp (93 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell930_product_lower
  have hD : Real.exp (Real.pi * Real.exp (931 / 800 : ℝ) - (93 / 320 : ℝ)) ≤
      (174745029448767 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell930_denomUpper
    linarith [hpThetaJensenCell930_product_upper]
  have hi : (1 / (174745029448767 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (931 / 800 : ℝ) - (93 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (174745029448767 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (174745029448767 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((93 / 320 : ℝ) - Real.pi * Real.exp (931 / 800 : ℝ)) := by
    rw [show (93 / 320 : ℝ) - Real.pi * Real.exp (931 / 800 : ℝ) =
      -(Real.pi * Real.exp (931 / 800 : ℝ) - (93 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (93 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (93 / 80 : ℝ)) := by
    have h := hpThetaJensenCell930_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (174745029448767 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell930_endpointUpper :
    hpThetaJensenKernelEndpointUpper (93 / 160 : ℝ) (931 / 1600 : ℝ) ≤ (400323651 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (931 / 800 : ℝ)) (100591231229093969 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (931 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell930_product_upper
  have hD : (172508444628789 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (93 / 80 : ℝ) - (931 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell930_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell930_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (93 / 80 : ℝ) - (931 / 3200 : ℝ)) ≤
      (1 / (172508444628789 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (172508444628789 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((931 / 3200 : ℝ) - Real.pi * Real.exp (93 / 80 : ℝ)) ≤
      (2 / (172508444628789 / 10000000000 : ℝ) : ℝ) := by
    rw [show (931 / 3200 : ℝ) - Real.pi * Real.exp (93 / 80 : ℝ) =
      -(Real.pi * Real.exp (93 / 80 : ℝ) - (931 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (100591231229093969 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (100591231229093969 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell930_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (93 / 160 : ℝ) (931 / 1600 : ℝ)) :
    (393091187 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (400323651 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell930_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell930_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell931_leftExp :
    (32019179831 / 10000000000 : ℝ) ≤ Real.exp (931 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (931 / 800 : ℝ) (259259140863 / 250000000000 : ℝ)
    (32019179831 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell931_rightExp :
    Real.exp (233 / 200 : ℝ) ≤ (32059228833 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (233 / 200 : ℝ) (207415414697 / 200000000000 : ℝ)
    (32059228833 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell931_denomUpper :
    Real.exp (97807673887150969 / 10000000000000000 : ℝ) ≤ (176902229230503 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (97807673887150969 / 10000000000000000 : ℝ)
    (1357505712469 / 1000000000000 : ℝ) (176902229230503 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell931_denomLower :
    (87317644324109 / 5000000000 : ℝ) ≤ Real.exp (12209837400453869 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (12209837400453869 / 1250000000000000 : ℝ) (678479342811
    / 500000000000 : ℝ) (87317644324109 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell931_product_lower :
    (12573899900453869 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (931 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell931_leftExp
    (by norm_num : (0 : ℝ) ≤ (32019179831 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell931_product_upper :
    Real.pi * Real.exp (233 / 200 : ℝ) ≤ (100717048887150969 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell931_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell931_endpointLower :
    (389355019 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (931 / 1600 : ℝ) (233 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12573899900453869 / 1250000000000000 : ℝ) (Real.pi * Real.exp (931 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell931_product_lower
  have hD : Real.exp (Real.pi * Real.exp (233 / 200 : ℝ) - (931 / 3200 : ℝ)) ≤
      (176902229230503 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell931_denomUpper
    linarith [hpThetaJensenCell931_product_upper]
  have hi : (1 / (176902229230503 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (233 / 200 : ℝ) - (931 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (176902229230503 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (176902229230503 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((931 / 3200 : ℝ) - Real.pi * Real.exp (233 / 200 : ℝ)) := by
    rw [show (931 / 3200 : ℝ) - Real.pi * Real.exp (233 / 200 : ℝ) =
      -(Real.pi * Real.exp (233 / 200 : ℝ) - (931 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (931 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (931 / 800 : ℝ)) := by
    have h := hpThetaJensenCell931_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (176902229230503 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell931_endpointUpper :
    hpThetaJensenKernelEndpointUpper (931 / 1600 : ℝ) (233 / 400 : ℝ) ≤ (24782803 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (233 / 200 : ℝ)) (100717048887150969 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (233 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell931_product_upper
  have hD : (87317644324109 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (931 / 800 : ℝ) - (233 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell931_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell931_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (931 / 800 : ℝ) - (233 / 800 : ℝ)) ≤
      (1 / (87317644324109 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (87317644324109 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((233 / 800 : ℝ) - Real.pi * Real.exp (931 / 800 : ℝ)) ≤
      (2 / (87317644324109 / 5000000000 : ℝ) : ℝ) := by
    rw [show (233 / 800 : ℝ) - Real.pi * Real.exp (931 / 800 : ℝ) =
      -(Real.pi * Real.exp (931 / 800 : ℝ) - (233 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (100717048887150969 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (100717048887150969 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell931_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (931 / 1600 : ℝ) (233 / 400 : ℝ)) :
    (389355019 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (24782803 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell931_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell931_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell932_leftExp :
    (32059228831 / 10000000000 : ℝ) ≤ Real.exp (233 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (233 / 200 : ℝ) (259269268371 / 250000000000 : ℝ)
    (32059228831 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell932_rightExp :
    Real.exp (933 / 800 : ℝ) ≤ (1283973117 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (933 / 800 : ℝ) (1037117585099 / 1000000000000 : ℝ)
    (1283973117 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell932_denomUpper :
    Real.exp (3917220956555381 / 400000000000000 : ℝ) ≤ (179088877579011 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3917220956555381 / 400000000000000 : ℝ) (33950674189 /
    25000000000 : ℝ) (179088877579011 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell932_denomLower :
    (35358226597561 / 2000000000 : ℝ) ≤ Real.exp (12225173977704869 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (12225173977704869 / 1250000000000000 : ℝ) (678739531459
    / 500000000000 : ℝ) (35358226597561 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell932_product_lower :
    (12589627102704869 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (233 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell932_leftExp
    (by norm_num : (0 : ℝ) ≤ (32059228831 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell932_product_upper :
    Real.pi * Real.exp (933 / 800 : ℝ) ≤ (4033720956555381 / 400000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell932_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell932_endpointLower :
    (385648169 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (233 / 400 : ℝ) (933 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12589627102704869 / 1250000000000000 : ℝ) (Real.pi * Real.exp (233 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell932_product_lower
  have hD : Real.exp (Real.pi * Real.exp (933 / 800 : ℝ) - (233 / 800 : ℝ)) ≤
      (179088877579011 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell932_denomUpper
    linarith [hpThetaJensenCell932_product_upper]
  have hi : (1 / (179088877579011 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (933 / 800 : ℝ) - (233 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (179088877579011 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (179088877579011 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((233 / 800 : ℝ) - Real.pi * Real.exp (933 / 800 : ℝ)) := by
    rw [show (233 / 800 : ℝ) - Real.pi * Real.exp (933 / 800 : ℝ) =
      -(Real.pi * Real.exp (933 / 800 : ℝ) - (233 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (233 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (233 / 200 : ℝ)) := by
    have h := hpThetaJensenCell932_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (179088877579011 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell932_endpointUpper :
    hpThetaJensenKernelEndpointUpper (233 / 400 : ℝ) (933 / 1600 : ℝ) ≤ (392755793 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (933 / 800 : ℝ)) (4033720956555381 / 400000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (933 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell932_product_upper
  have hD : (35358226597561 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (233 / 200 : ℝ) - (933 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell932_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell932_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (233 / 200 : ℝ) - (933 / 3200 : ℝ)) ≤
      (1 / (35358226597561 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (35358226597561 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((933 / 3200 : ℝ) - Real.pi * Real.exp (233 / 200 : ℝ)) ≤
      (2 / (35358226597561 / 2000000000 : ℝ) : ℝ) := by
    rw [show (933 / 3200 : ℝ) - Real.pi * Real.exp (233 / 200 : ℝ) =
      -(Real.pi * Real.exp (233 / 200 : ℝ) - (933 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4033720956555381 / 400000000000000 : ℝ) ^ 2 - 6 *
      (4033720956555381 / 400000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell932_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (233 / 400 : ℝ) (933 / 1600 : ℝ)) :
    (385648169 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (392755793 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell932_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell932_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell933_leftExp :
    (32099327923 / 10000000000 : ℝ) ≤ Real.exp (933 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (933 / 800 : ℝ) (518558792549 / 500000000000 : ℝ)
    (32099327923 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell933_rightExp :
    Real.exp (467 / 400 : ℝ) ≤ (32139477173 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (467 / 400 : ℝ) (129644762287 / 125000000000 : ℝ)
    (32139477173 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell933_denomUpper :
    Real.exp (98053531510356589 / 10000000000000000 : ℝ) ≤ (181305411396953 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (98053531510356589 / 10000000000000000 : ℝ) (16981863647
    / 12500000000 : ℝ) (181305411396953 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell933_denomLower :
    (35795281476689 / 2000000000 : ℝ) ≤ Real.exp (12240530226034177 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (12240530226034177 / 1250000000000000 : ℝ) (679000153803
    / 500000000000 : ℝ) (35795281476689 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell933_product_lower :
    (12605373976034177 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (933 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell933_leftExp
    (by norm_num : (0 : ℝ) ≤ (32099327923 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell933_product_upper :
    Real.pi * Real.exp (467 / 400 : ℝ) ≤ (100969156510356589 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell933_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell933_endpointLower :
    (95492617 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (933 / 1600 : ℝ) (467 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12605373976034177 / 1250000000000000 : ℝ) (Real.pi * Real.exp (933 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell933_product_lower
  have hD : Real.exp (Real.pi * Real.exp (467 / 400 : ℝ) - (933 / 3200 : ℝ)) ≤
      (181305411396953 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell933_denomUpper
    linarith [hpThetaJensenCell933_product_upper]
  have hi : (1 / (181305411396953 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (467 / 400 : ℝ) - (933 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (181305411396953 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (181305411396953 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((933 / 3200 : ℝ) - Real.pi * Real.exp (467 / 400 : ℝ)) := by
    rw [show (933 / 3200 : ℝ) - Real.pi * Real.exp (467 / 400 : ℝ) =
      -(Real.pi * Real.exp (467 / 400 : ℝ) - (933 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (933 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (933 / 800 : ℝ)) := by
    have h := hpThetaJensenCell933_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (181305411396953 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell933_endpointUpper :
    hpThetaJensenKernelEndpointUpper (933 / 1600 : ℝ) (467 / 800 : ℝ) ≤ (194508159 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (467 / 400 : ℝ)) (100969156510356589 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (467 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell933_product_upper
  have hD : (35795281476689 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (933 / 800 : ℝ) - (467 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell933_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell933_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (933 / 800 : ℝ) - (467 / 1600 : ℝ)) ≤
      (1 / (35795281476689 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (35795281476689 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((467 / 1600 : ℝ) - Real.pi * Real.exp (933 / 800 : ℝ)) ≤
      (2 / (35795281476689 / 2000000000 : ℝ) : ℝ) := by
    rw [show (467 / 1600 : ℝ) - Real.pi * Real.exp (933 / 800 : ℝ) =
      -(Real.pi * Real.exp (933 / 800 : ℝ) - (467 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (100969156510356589 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (100969156510356589 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell933_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (933 / 1600 : ℝ) (467 / 800 : ℝ)) :
    (95492617 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (194508159 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell933_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell933_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell934_leftExp :
    (32139477171 / 10000000000 : ℝ) ≤ Real.exp (467 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (467 / 400 : ℝ) (207431619659 / 200000000000 : ℝ)
    (32139477171 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell934_rightExp :
    Real.exp (187 / 160 : ℝ) ≤ (201122979 / 62500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (187 / 160 : ℝ) (259299653269 / 250000000000 : ℝ)
    (201122979 / 62500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell934_denomUpper :
    Real.exp (613604355465547 / 62500000000000 : ℝ) ≤ (91776137238647 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (613604355465547 / 62500000000000 : ℝ) (339768021689 /
    250000000000 : ℝ) (91776137238647 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell934_denomLower :
    (181191548458961 / 10000000000 : ℝ) ≤ Real.exp (12255906170574529 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (12255906170574529 / 1250000000000000 : ℝ) (271704484277
    / 200000000000 : ℝ) (181191548458961 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell934_product_lower :
    (12621140545574529 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (467 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell934_leftExp
    (by norm_num : (0 : ℝ) ≤ (32139477171 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell934_product_upper :
    Real.pi * Real.exp (187 / 160 : ℝ) ≤ (631846542965547 / 62500000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell934_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell934_endpointLower :
    (378321749 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (467 / 800 : ℝ) (187 / 320 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12621140545574529 / 1250000000000000 : ℝ) (Real.pi * Real.exp (467 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell934_product_lower
  have hD : Real.exp (Real.pi * Real.exp (187 / 160 : ℝ) - (467 / 1600 : ℝ)) ≤
      (91776137238647 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell934_denomUpper
    linarith [hpThetaJensenCell934_product_upper]
  have hi : (1 / (91776137238647 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (187 / 160 : ℝ) - (467 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (91776137238647 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (91776137238647 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((467 / 1600 : ℝ) - Real.pi * Real.exp (187 / 160 : ℝ)) := by
    rw [show (467 / 1600 : ℝ) - Real.pi * Real.exp (187 / 160 : ℝ) =
      -(Real.pi * Real.exp (187 / 160 : ℝ) - (467 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (467 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (467 / 400 : ℝ)) := by
    have h := hpThetaJensenCell934_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (91776137238647 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell934_endpointUpper :
    hpThetaJensenKernelEndpointUpper (467 / 800 : ℝ) (187 / 320 : ℝ) ≤ (385306251 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (187 / 160 : ℝ)) (631846542965547 / 62500000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (187 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell934_product_upper
  have hD : (181191548458961 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (467 / 400 : ℝ) - (187 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell934_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell934_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (467 / 400 : ℝ) - (187 / 640 : ℝ)) ≤
      (1 / (181191548458961 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (181191548458961 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((187 / 640 : ℝ) - Real.pi * Real.exp (467 / 400 : ℝ)) ≤
      (2 / (181191548458961 / 10000000000 : ℝ) : ℝ) := by
    rw [show (187 / 640 : ℝ) - Real.pi * Real.exp (467 / 400 : ℝ) =
      -(Real.pi * Real.exp (467 / 400 : ℝ) - (187 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (631846542965547 / 62500000000000 : ℝ) ^ 2 - 6 *
      (631846542965547 / 62500000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell934_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (467 / 800 : ℝ) (187 / 320 : ℝ)) :
    (378321749 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (385306251 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell934_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell934_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell935_leftExp :
    (16089838319 / 5000000000 : ℝ) ≤ Real.exp (187 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (187 / 160 : ℝ) (41487944523 / 40000000000 : ℝ)
    (16089838319 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell935_rightExp :
    Real.exp (117 / 100 : ℝ) ≤ (16109963193 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (117 / 100 : ℝ) (518619564719 / 500000000000 : ℝ)
    (16109963193 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell935_denomUpper :
    Real.exp (49150010097386449 / 5000000000000000 : ℝ) ≤ (185829917529619 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (49150010097386449 / 5000000000000000 : ℝ) (679797977101
    / 500000000000 : ℝ) (185829917529619 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell935_denomLower :
    (45859249934227 / 2500000000 : ℝ) ≤ Real.exp (6135650918032981 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6135650918032981 / 625000000000000 : ℝ) (169880675743 /
    125000000000 : ℝ) (45859249934227 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell935_product_lower :
    (6318463418032981 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (187 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell935_leftExp
    (by norm_num : (0 : ℝ) ≤ (16089838319 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell935_product_upper :
    Real.pi * Real.exp (117 / 100 : ℝ) ≤ (50610947597386449 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell935_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell935_endpointLower :
    (187350923 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (187 / 320 : ℝ) (117 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6318463418032981 / 625000000000000 : ℝ) (Real.pi * Real.exp (187 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell935_product_lower
  have hD : Real.exp (Real.pi * Real.exp (117 / 100 : ℝ) - (187 / 640 : ℝ)) ≤
      (185829917529619 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell935_denomUpper
    linarith [hpThetaJensenCell935_product_upper]
  have hi : (1 / (185829917529619 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (117 / 100 : ℝ) - (187 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (185829917529619 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (185829917529619 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((187 / 640 : ℝ) - Real.pi * Real.exp (117 / 100 : ℝ)) := by
    rw [show (187 / 640 : ℝ) - Real.pi * Real.exp (117 / 100 : ℝ) =
      -(Real.pi * Real.exp (117 / 100 : ℝ) - (187 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (187 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (187 / 160 : ℝ)) := by
    have h := hpThetaJensenCell935_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (185829917529619 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell935_endpointUpper :
    hpThetaJensenKernelEndpointUpper (187 / 320 : ℝ) (117 / 200 : ℝ) ≤ (15265017 / 400000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (117 / 100 : ℝ)) (50610947597386449 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (117 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell935_product_upper
  have hD : (45859249934227 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (187 / 160 : ℝ) - (117 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell935_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell935_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (187 / 160 : ℝ) - (117 / 400 : ℝ)) ≤
      (1 / (45859249934227 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (45859249934227 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((117 / 400 : ℝ) - Real.pi * Real.exp (187 / 160 : ℝ)) ≤
      (2 / (45859249934227 / 2500000000 : ℝ) : ℝ) := by
    rw [show (117 / 400 : ℝ) - Real.pi * Real.exp (187 / 160 : ℝ) =
      -(Real.pi * Real.exp (187 / 160 : ℝ) - (117 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (50610947597386449 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (50610947597386449 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell935_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (187 / 320 : ℝ) (117 / 200 : ℝ)) :
    (187350923 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15265017 / 400000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell935_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell935_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell936_leftExp :
    (2013745399 / 625000000 : ℝ) ≤ Real.exp (117 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (117 / 100 : ℝ) (1037239129437 / 1000000000000 : ℝ)
    (2013745399 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell936_rightExp :
    Real.exp (937 / 800 : ℝ) ≤ (32260226477 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (937 / 800 : ℝ) (1037279647383 / 1000000000000 : ℝ)
    (32260226477 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell936_denomUpper :
    Real.exp (98423501678557861 / 10000000000000000 : ℝ) ≤ (188138798795209 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (98423501678557861 / 10000000000000000 : ℝ)
    (1360120695833 / 1000000000000 : ℝ) (188138798795209 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell936_denomLower :
    (46428302907667 / 2500000000 : ℝ) ≤ Real.exp (767919827879401 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (767919827879401 / 78125000000000 : ℝ) (679784631467 /
    500000000000 : ℝ) (46428302907667 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell936_product_lower :
    (790795804441901 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (117 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell936_leftExp
    (by norm_num : (0 : ℝ) ≤ (2013745399 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell936_product_upper :
    Real.pi * Real.exp (937 / 800 : ℝ) ≤ (101348501678557861 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell936_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell936_endpointLower :
    (37111059 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (117 / 200 : ℝ) (937 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (790795804441901 / 78125000000000 : ℝ) (Real.pi * Real.exp (117 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell936_product_lower
  have hD : Real.exp (Real.pi * Real.exp (937 / 800 : ℝ) - (117 / 400 : ℝ)) ≤
      (188138798795209 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell936_denomUpper
    linarith [hpThetaJensenCell936_product_upper]
  have hi : (1 / (188138798795209 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (937 / 800 : ℝ) - (117 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (188138798795209 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (188138798795209 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((117 / 400 : ℝ) - Real.pi * Real.exp (937 / 800 : ℝ)) := by
    rw [show (117 / 400 : ℝ) - Real.pi * Real.exp (937 / 800 : ℝ) =
      -(Real.pi * Real.exp (937 / 800 : ℝ) - (117 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (117 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (117 / 100 : ℝ)) := by
    have h := hpThetaJensenCell936_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (188138798795209 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell936_endpointUpper :
    hpThetaJensenKernelEndpointUpper (117 / 200 : ℝ) (937 / 1600 : ℝ) ≤ (377973671 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (937 / 800 : ℝ)) (101348501678557861 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (937 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell936_product_upper
  have hD : (46428302907667 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (117 / 100 : ℝ) - (937 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell936_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell936_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (117 / 100 : ℝ) - (937 / 3200 : ℝ)) ≤
      (1 / (46428302907667 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (46428302907667 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((937 / 3200 : ℝ) - Real.pi * Real.exp (117 / 100 : ℝ)) ≤
      (2 / (46428302907667 / 2500000000 : ℝ) : ℝ) := by
    rw [show (937 / 3200 : ℝ) - Real.pi * Real.exp (117 / 100 : ℝ) =
      -(Real.pi * Real.exp (117 / 100 : ℝ) - (937 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (101348501678557861 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (101348501678557861 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell936_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (117 / 200 : ℝ) (937 / 1600 : ℝ)) :
    (37111059 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (377973671 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell936_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell936_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell937_leftExp :
    (1290409059 / 400000000 : ℝ) ≤ Real.exp (937 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (937 / 800 : ℝ) (518639823691 / 500000000000 : ℝ)
    (1290409059 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell937_rightExp :
    Real.exp (469 / 400 : ℝ) ≤ (32300576973 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (469 / 400 : ℝ) (103732016691 / 100000000000 : ℝ)
    (32300576973 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell937_denomUpper :
    Real.exp (98547141514337989 / 10000000000000000 : ℝ) ≤ (4761984586711 / 250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (98547141514337989 / 10000000000000000 : ℝ) (170080789163
    / 125000000000 : ℝ) (4761984586711 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell937_denomLower :
    (367227816597 / 19531250 : ℝ) ≤ Real.exp (492086097060241 / 50000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (492086097060241 / 50000000000000 : ℝ) (1360093994091 /
    1000000000000 : ℝ) (367227816597 / 19531250 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell937_product_lower :
    (506742347060241 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (937 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell937_leftExp
    (by norm_num : (0 : ℝ) ≤ (1290409059 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell937_product_upper :
    Real.pi * Real.exp (469 / 400 : ℝ) ≤ (101475266514337989 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell937_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell937_endpointLower :
    (367547817 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (937 / 1600 : ℝ) (469 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (506742347060241 / 50000000000000 : ℝ) (Real.pi * Real.exp (937 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell937_product_lower
  have hD : Real.exp (Real.pi * Real.exp (469 / 400 : ℝ) - (937 / 3200 : ℝ)) ≤
      (4761984586711 / 250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell937_denomUpper
    linarith [hpThetaJensenCell937_product_upper]
  have hi : (1 / (4761984586711 / 250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (469 / 400 : ℝ) - (937 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4761984586711 / 250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4761984586711 / 250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((937 / 3200 : ℝ) - Real.pi * Real.exp (469 / 400 : ℝ)) := by
    rw [show (937 / 3200 : ℝ) - Real.pi * Real.exp (469 / 400 : ℝ) =
      -(Real.pi * Real.exp (469 / 400 : ℝ) - (937 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (937 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (937 / 800 : ℝ)) := by
    have h := hpThetaJensenCell937_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4761984586711 / 250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell937_endpointUpper :
    hpThetaJensenKernelEndpointUpper (937 / 1600 : ℝ) (469 / 800 : ℝ) ≤ (18717541 / 500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (469 / 400 : ℝ)) (101475266514337989 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (469 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell937_product_upper
  have hD : (367227816597 / 19531250 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (937 / 800 : ℝ) - (469 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell937_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell937_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (937 / 800 : ℝ) - (469 / 1600 : ℝ)) ≤
      (1 / (367227816597 / 19531250 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (367227816597 / 19531250 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((469 / 1600 : ℝ) - Real.pi * Real.exp (937 / 800 : ℝ)) ≤
      (2 / (367227816597 / 19531250 : ℝ) : ℝ) := by
    rw [show (469 / 1600 : ℝ) - Real.pi * Real.exp (937 / 800 : ℝ) =
      -(Real.pi * Real.exp (937 / 800 : ℝ) - (469 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (101475266514337989 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (101475266514337989 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell937_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (937 / 1600 : ℝ) (469 / 800 : ℝ)) :
    (367547817 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (18717541 / 500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell937_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell937_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell938_leftExp :
    (32300576971 / 10000000000 : ℝ) ≤ Real.exp (469 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (469 / 400 : ℝ) (1037320166909 / 1000000000000 : ℝ)
    (32300576971 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell938_rightExp :
    Real.exp (939 / 800 : ℝ) ≤ (1617048897 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (939 / 800 : ℝ) (1037360688021 / 1000000000000 : ℝ)
    (1617048897 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell938_denomUpper :
    Real.exp (4933546995472921 / 500000000000000 : ℝ) ≤ (192852144565143 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4933546995472921 / 500000000000000 : ℝ) (1361172808359 /
    1000000000000 : ℝ) (192852144565143 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell938_denomLower :
    (38071951210641 / 2000000000 : ℝ) ≤ Real.exp (12317607400934729 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (12317607400934729 / 1250000000000000 : ℝ) (1360619601073
    / 1000000000000 : ℝ) (38071951210641 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell938_product_lower :
    (12684404275934729 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (469 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell938_leftExp
    (by norm_num : (0 : ℝ) ≤ (32300576971 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell938_product_upper :
    Real.pi * Real.exp (939 / 800 : ℝ) ≤ (5080109495472921 / 500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell938_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell938_endpointLower :
    (4550167 / 125000000 : ℝ) ≤ hpThetaTraceEndpointLower (469 / 800 : ℝ) (939 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12684404275934729 / 1250000000000000 : ℝ) (Real.pi * Real.exp (469 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell938_product_lower
  have hD : Real.exp (Real.pi * Real.exp (939 / 800 : ℝ) - (469 / 1600 : ℝ)) ≤
      (192852144565143 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell938_denomUpper
    linarith [hpThetaJensenCell938_product_upper]
  have hi : (1 / (192852144565143 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (939 / 800 : ℝ) - (469 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (192852144565143 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (192852144565143 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((469 / 1600 : ℝ) - Real.pi * Real.exp (939 / 800 : ℝ)) := by
    rw [show (469 / 1600 : ℝ) - Real.pi * Real.exp (939 / 800 : ℝ) =
      -(Real.pi * Real.exp (939 / 800 : ℝ) - (469 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (469 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (469 / 400 : ℝ)) := by
    have h := hpThetaJensenCell938_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (192852144565143 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell938_endpointUpper :
    hpThetaJensenKernelEndpointUpper (469 / 800 : ℝ) (939 / 1600 : ℝ) ≤ (74151341 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (939 / 800 : ℝ)) (5080109495472921 / 500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (939 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell938_product_upper
  have hD : (38071951210641 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (469 / 400 : ℝ) - (939 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell938_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell938_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (469 / 400 : ℝ) - (939 / 3200 : ℝ)) ≤
      (1 / (38071951210641 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (38071951210641 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((939 / 3200 : ℝ) - Real.pi * Real.exp (469 / 400 : ℝ)) ≤
      (2 / (38071951210641 / 2000000000 : ℝ) : ℝ) := by
    rw [show (939 / 3200 : ℝ) - Real.pi * Real.exp (469 / 400 : ℝ) =
      -(Real.pi * Real.exp (469 / 400 : ℝ) - (939 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (5080109495472921 / 500000000000000 : ℝ) ^ 2 - 6 *
      (5080109495472921 / 500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell938_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (469 / 800 : ℝ) (939 / 1600 : ℝ)) :
    (4550167 / 125000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (74151341 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell938_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell938_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell939_leftExp :
    (16170488969 / 5000000000 : ℝ) ≤ Real.exp (939 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (939 / 800 : ℝ) (51868034401 / 50000000000 : ℝ)
    (16170488969 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell939_rightExp :
    Real.exp (47 / 40 : ℝ) ≤ (32381429439 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (47 / 40 : ℝ) (518700605357 / 500000000000 : ℝ)
    (32381429439 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell939_denomUpper :
    Real.exp (98794897055556327 / 10000000000000000 : ℝ) ≤ (195257562347369 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (98794897055556327 / 10000000000000000 : ℝ)
    (1361700182673 / 1000000000000 : ℝ) (195257562347369 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell939_denomLower :
    (192731026193539 / 10000000000 : ℝ) ≤ Real.exp (6166541097637331 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6166541097637331 / 625000000000000 : ℝ) (1361146085619 /
    1000000000000 : ℝ) (192731026193539 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell939_product_lower :
    (6350134847637331 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (939 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell939_leftExp
    (by norm_num : (0 : ℝ) ≤ (16170488969 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell939_product_upper :
    Real.pi * Real.exp (47 / 40 : ℝ) ≤ (101729272055556327 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell939_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell939_endpointLower :
    (360507053 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (939 / 1600 : ℝ) (47 / 80 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6350134847637331 / 625000000000000 : ℝ) (Real.pi * Real.exp (939 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell939_product_lower
  have hD : Real.exp (Real.pi * Real.exp (47 / 40 : ℝ) - (939 / 3200 : ℝ)) ≤
      (195257562347369 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell939_denomUpper
    linarith [hpThetaJensenCell939_product_upper]
  have hi : (1 / (195257562347369 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (47 / 40 : ℝ) - (939 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (195257562347369 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (195257562347369 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((939 / 3200 : ℝ) - Real.pi * Real.exp (47 / 40 : ℝ)) := by
    rw [show (939 / 3200 : ℝ) - Real.pi * Real.exp (47 / 40 : ℝ) =
      -(Real.pi * Real.exp (47 / 40 : ℝ) - (939 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (939 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (939 / 800 : ℝ)) := by
    have h := hpThetaJensenCell939_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (195257562347369 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell939_endpointUpper :
    hpThetaJensenKernelEndpointUpper (939 / 1600 : ℝ) (47 / 80 : ℝ) ≤ (183595579 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (47 / 40 : ℝ)) (101729272055556327 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (47 / 80 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell939_product_upper
  have hD : (192731026193539 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (939 / 800 : ℝ) - (47 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell939_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell939_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (939 / 800 : ℝ) - (47 / 160 : ℝ)) ≤
      (1 / (192731026193539 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (192731026193539 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((47 / 160 : ℝ) - Real.pi * Real.exp (939 / 800 : ℝ)) ≤
      (2 / (192731026193539 / 10000000000 : ℝ) : ℝ) := by
    rw [show (47 / 160 : ℝ) - Real.pi * Real.exp (939 / 800 : ℝ) =
      -(Real.pi * Real.exp (939 / 800 : ℝ) - (47 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (101729272055556327 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (101729272055556327 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell939_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (939 / 1600 : ℝ) (47 / 80 : ℝ)) :
    (360507053 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (183595579 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell939_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell939_endpointUpper

def hpThetaJensenCellsBatch046Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (216051281 / 5000000000 : ℝ)
  | 1 => (85612779 / 2000000000 : ℝ)
  | 2 => (424056247 / 10000000000 : ℝ)
  | 3 => (210039723 / 5000000000 : ℝ)
  | 4 => (416133319 / 10000000000 : ℝ)
  | 5 => (412217697 / 10000000000 : ℝ)
  | 6 => (51041551 / 1250000000 : ℝ)
  | 7 => (202238641 / 5000000000 : ℝ)
  | 8 => (8013043 / 200000000 : ℝ)
  | 9 => (396856841 / 10000000000 : ℝ)
  | 10 => (393091187 / 10000000000 : ℝ)
  | 11 => (389355019 / 10000000000 : ℝ)
  | 12 => (385648169 / 10000000000 : ℝ)
  | 13 => (95492617 / 2500000000 : ℝ)
  | 14 => (378321749 / 10000000000 : ℝ)
  | 15 => (187350923 / 5000000000 : ℝ)
  | 16 => (37111059 / 1000000000 : ℝ)
  | 17 => (367547817 / 10000000000 : ℝ)
  | 18 => (4550167 / 125000000 : ℝ)
  | 19 => (360507053 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch046Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (5499819 / 125000000 : ℝ)
  | 1 => (2179399 / 50000000 : ℝ)
  | 2 => (431805549 / 10000000000 : ℝ)
  | 3 => (427762593 / 10000000000 : ℝ)
  | 4 => (211875379 / 5000000000 : ℝ)
  | 5 => (419769873 / 10000000000 : ℝ)
  | 6 => (103954941 / 2500000000 : ℝ)
  | 7 => (205950129 / 5000000000 : ℝ)
  | 8 => (204005593 / 5000000000 : ℝ)
  | 9 => (404152373 / 10000000000 : ℝ)
  | 10 => (400323651 / 10000000000 : ℝ)
  | 11 => (24782803 / 625000000 : ℝ)
  | 12 => (392755793 / 10000000000 : ℝ)
  | 13 => (194508159 / 5000000000 : ℝ)
  | 14 => (385306251 / 10000000000 : ℝ)
  | 15 => (15265017 / 400000000 : ℝ)
  | 16 => (377973671 / 10000000000 : ℝ)
  | 17 => (18717541 / 500000000 : ℝ)
  | 18 => (74151341 / 2000000000 : ℝ)
  | 19 => (183595579 / 5000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch046_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((920 : ℝ) + (j.val : ℝ)) / 1600)
      (((920 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch046Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch046Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell920_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell921_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell922_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell923_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell924_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell925_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell926_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell927_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell928_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell929_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell930_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell931_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell932_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell933_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell934_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell935_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell936_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell937_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell938_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell939_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper] at h ⊢
    exact h

end HodgeProofHP
