import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell80_leftExp :
    (552585459 / 500000000 : ℝ) ≤ Real.exp (1 / 10 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1 / 10 : ℝ) (501564943951 / 500000000000 : ℝ) (552585459
    / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell80_rightExp :
    Real.exp (81 / 800 : ℝ) ≤ (1383191557 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (81 / 800 : ℝ) (100316907343 / 100000000000 : ℝ)
    (1383191557 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell80_denomUpper :
    Real.exp (4314174913130301 / 1250000000000000 : ℝ) ≤ (63085257873 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4314174913130301 / 1250000000000000 : ℝ) (1113885521577
    / 1000000000000 : ℝ) (63085257873 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell80_denomLower :
    (156980489519 / 5000000000 : ℝ) ≤ Real.exp (215417725913841 / 62500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (215417725913841 / 62500000000000 : ℝ) (1113723452029 /
    1000000000000 : ℝ) (156980489519 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell80_product_lower :
    (216999757163841 / 62500000000000 : ℝ) ≤ Real.pi * Real.exp (1 / 10 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell80_leftExp
    (by norm_num : (0 : ℝ) ≤ (552585459 / 500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell80_product_upper :
    Real.pi * Real.exp (81 / 800 : ℝ) ≤ (4345424913130301 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell80_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell80_endpointLower :
    (1736510387 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 20 : ℝ) (81 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (216999757163841 / 62500000000000 : ℝ) (Real.pi * Real.exp (1 / 10 : ℝ))
    (by norm_num) hpThetaJensenCell80_product_lower
  have hD : Real.exp (Real.pi * Real.exp (81 / 800 : ℝ) - (1 / 40 : ℝ)) ≤
      (63085257873 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell80_denomUpper
    linarith [hpThetaJensenCell80_product_upper]
  have hi : (1 / (63085257873 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (81 / 800 : ℝ) - (1 / 40 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (63085257873 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (63085257873 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1 / 40 : ℝ) - Real.pi * Real.exp (81 / 800 : ℝ)) := by
    rw [show (1 / 40 : ℝ) - Real.pi * Real.exp (81 / 800 : ℝ) =
      -(Real.pi * Real.exp (81 / 800 : ℝ) - (1 / 40 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1 / 10 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1 / 10 : ℝ)) := by
    have h := hpThetaJensenCell80_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (63085257873 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell80_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1 / 20 : ℝ) (81 / 1600 : ℝ) ≤ (8776279023 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (81 / 800 : ℝ)) (4345424913130301 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (81 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell80_product_upper
  have hD : (156980489519 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1 / 10 : ℝ) - (81 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell80_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell80_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1 / 10 : ℝ) - (81 / 3200 : ℝ)) ≤
      (1 / (156980489519 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (156980489519 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((81 / 3200 : ℝ) - Real.pi * Real.exp (1 / 10 : ℝ)) ≤
      (2 / (156980489519 / 5000000000 : ℝ) : ℝ) := by
    rw [show (81 / 3200 : ℝ) - Real.pi * Real.exp (1 / 10 : ℝ) =
      -(Real.pi * Real.exp (1 / 10 : ℝ) - (81 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4345424913130301 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (4345424913130301 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell80_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1 / 20 : ℝ) (81 / 1600 : ℝ)) :
    (1736510387 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8776279023 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell80_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell80_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell81_leftExp :
    (5532766227 / 5000000000 : ℝ) ≤ Real.exp (81 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (81 / 800 : ℝ) (1003169073429 / 1000000000000 : ℝ)
    (5532766227 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell81_rightExp :
    Real.exp (41 / 400 : ℝ) ≤ (553968651 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (41 / 400 : ℝ) (1003208260487 / 1000000000000 : ℝ)
    (553968651 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell81_denomUpper :
    Real.exp (1727687786201043 / 500000000000000 : ℝ) ≤ (316701808957 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1727687786201043 / 500000000000000 : ℝ) (557013003391 /
    500000000000 : ℝ) (316701808957 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell81_denomLower :
    (39403607563 / 1250000000 : ℝ) ≤ Real.exp (2156696139576673 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2156696139576673 / 625000000000000 : ℝ) (1113863727673 /
    1000000000000 : ℝ) (39403607563 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell81_product_lower :
    (2172711764576673 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (81 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell81_leftExp
    (by norm_num : (0 : ℝ) ≤ (5532766227 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell81_product_upper :
    Real.pi * Real.exp (41 / 400 : ℝ) ≤ (1740344036201043 / 500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell81_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell81_endpointLower :
    (17354933089 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (81 / 1600 : ℝ) (41 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2172711764576673 / 625000000000000 : ℝ) (Real.pi * Real.exp (81 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell81_product_lower
  have hD : Real.exp (Real.pi * Real.exp (41 / 400 : ℝ) - (81 / 3200 : ℝ)) ≤
      (316701808957 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell81_denomUpper
    linarith [hpThetaJensenCell81_product_upper]
  have hi : (1 / (316701808957 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (41 / 400 : ℝ) - (81 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (316701808957 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (316701808957 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((81 / 3200 : ℝ) - Real.pi * Real.exp (41 / 400 : ℝ)) := by
    rw [show (81 / 3200 : ℝ) - Real.pi * Real.exp (41 / 400 : ℝ) =
      -(Real.pi * Real.exp (41 / 400 : ℝ) - (81 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (81 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (81 / 800 : ℝ)) := by
    have h := hpThetaJensenCell81_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (316701808957 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell81_endpointUpper :
    hpThetaJensenKernelEndpointUpper (81 / 1600 : ℝ) (41 / 800 : ℝ) ≤ (17542336181 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (41 / 400 : ℝ)) (1740344036201043 / 500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (41 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell81_product_upper
  have hD : (39403607563 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (81 / 800 : ℝ) - (41 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell81_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell81_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (81 / 800 : ℝ) - (41 / 1600 : ℝ)) ≤
      (1 / (39403607563 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (39403607563 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((41 / 1600 : ℝ) - Real.pi * Real.exp (81 / 800 : ℝ)) ≤
      (2 / (39403607563 / 1250000000 : ℝ) : ℝ) := by
    rw [show (41 / 1600 : ℝ) - Real.pi * Real.exp (81 / 800 : ℝ) =
      -(Real.pi * Real.exp (81 / 800 : ℝ) - (41 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1740344036201043 / 500000000000000 : ℝ) ^ 2 - 6 *
      (1740344036201043 / 500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell81_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (81 / 1600 : ℝ) (41 / 800 : ℝ)) :
    (17354933089 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17542336181 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell81_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell81_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell82_leftExp :
    (5539686509 / 5000000000 : ℝ) ≤ Real.exp (41 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (41 / 400 : ℝ) (501604130243 / 500000000000 : ℝ)
    (5539686509 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell82_rightExp :
    Real.exp (83 / 800 : ℝ) ≤ (2218646179 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (83 / 800 : ℝ) (40129897963 / 40000000000 : ℝ)
    (2218646179 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell82_denomUpper :
    Real.exp (6918833305423147 / 2000000000000000 : ℝ) ≤ (317984215811 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (6918833305423147 / 2000000000000000 : ℝ) (557083349529 /
    500000000000 : ℝ) (317984215811 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell82_denomLower :
    (158251790647 / 5000000000 : ℝ) ≤ Real.exp (2159218414897791 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2159218414897791 / 625000000000000 : ℝ) (1114004210081 /
    1000000000000 : ℝ) (158251790647 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell82_product_lower :
    (2175429352397791 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (41 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell82_leftExp
    (by norm_num : (0 : ℝ) ≤ (5539686509 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell82_product_upper :
    Real.pi * Real.exp (83 / 800 : ℝ) ≤ (6970083305423147 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell82_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell82_endpointLower :
    (4336159439 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (41 / 800 : ℝ) (83 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2175429352397791 / 625000000000000 : ℝ) (Real.pi * Real.exp (41 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell82_product_lower
  have hD : Real.exp (Real.pi * Real.exp (83 / 800 : ℝ) - (41 / 1600 : ℝ)) ≤
      (317984215811 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell82_denomUpper
    linarith [hpThetaJensenCell82_product_upper]
  have hi : (1 / (317984215811 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (83 / 800 : ℝ) - (41 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (317984215811 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (317984215811 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((41 / 1600 : ℝ) - Real.pi * Real.exp (83 / 800 : ℝ)) := by
    rw [show (41 / 1600 : ℝ) - Real.pi * Real.exp (83 / 800 : ℝ) =
      -(Real.pi * Real.exp (83 / 800 : ℝ) - (41 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (41 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (41 / 400 : ℝ)) := by
    have h := hpThetaJensenCell82_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (317984215811 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell82_endpointUpper :
    hpThetaJensenKernelEndpointUpper (41 / 800 : ℝ) (83 / 1600 : ℝ) ≤ (17531988579 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (83 / 800 : ℝ)) (6970083305423147 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (83 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell82_product_upper
  have hD : (158251790647 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (41 / 400 : ℝ) - (83 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell82_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell82_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (41 / 400 : ℝ) - (83 / 3200 : ℝ)) ≤
      (1 / (158251790647 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (158251790647 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((83 / 3200 : ℝ) - Real.pi * Real.exp (41 / 400 : ℝ)) ≤
      (2 / (158251790647 / 5000000000 : ℝ) : ℝ) := by
    rw [show (83 / 3200 : ℝ) - Real.pi * Real.exp (41 / 400 : ℝ) =
      -(Real.pi * Real.exp (41 / 400 : ℝ) - (83 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (6970083305423147 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (6970083305423147 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell82_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (41 / 800 : ℝ) (83 / 1600 : ℝ)) :
    (4336159439 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17531988579 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell82_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell82_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell83_leftExp :
    (5546615447 / 5000000000 : ℝ) ≤ Real.exp (83 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (83 / 800 : ℝ) (501623724537 / 500000000000 : ℝ)
    (5546615447 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell83_rightExp :
    Real.exp (21 / 200 : ℝ) ≤ (1388388263 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21 / 200 : ℝ) (501643319597 / 500000000000 : ℝ)
    (1388388263 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell83_denomUpper :
    Real.exp (4329328973322959 / 1250000000000000 : ℝ) ≤ (19954597131 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4329328973322959 / 1250000000000000 : ℝ) (111430759873 /
    100000000000 : ℝ) (19954597131 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell83_denomLower :
    (2542281481 / 80000000 : ℝ) ≤ Real.exp (2161744089421453 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2161744089421453 / 625000000000000 : ℝ) (557072449783 /
    500000000000 : ℝ) (2542281481 / 80000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell83_product_lower :
    (2178150339421453 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (83 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell83_leftExp
    (by norm_num : (0 : ℝ) ≤ (5546615447 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell83_product_upper :
    Real.pi * Real.exp (21 / 200 : ℝ) ≤ (4361750848322959 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell83_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell83_endpointLower :
    (4333554523 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (83 / 1600 : ℝ) (21 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2178150339421453 / 625000000000000 : ℝ) (Real.pi * Real.exp (83 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell83_product_lower
  have hD : Real.exp (Real.pi * Real.exp (21 / 200 : ℝ) - (83 / 3200 : ℝ)) ≤
      (19954597131 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell83_denomUpper
    linarith [hpThetaJensenCell83_product_upper]
  have hi : (1 / (19954597131 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (21 / 200 : ℝ) - (83 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (19954597131 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (19954597131 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((83 / 3200 : ℝ) - Real.pi * Real.exp (21 / 200 : ℝ)) := by
    rw [show (83 / 3200 : ℝ) - Real.pi * Real.exp (21 / 200 : ℝ) =
      -(Real.pi * Real.exp (21 / 200 : ℝ) - (83 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (83 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (83 / 800 : ℝ)) := by
    have h := hpThetaJensenCell83_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (19954597131 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell83_endpointUpper :
    hpThetaJensenKernelEndpointUpper (83 / 1600 : ℝ) (21 / 400 : ℝ) ≤ (17521515469 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (21 / 200 : ℝ)) (4361750848322959 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (21 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell83_product_upper
  have hD : (2542281481 / 80000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (83 / 800 : ℝ) - (21 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell83_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell83_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (83 / 800 : ℝ) - (21 / 800 : ℝ)) ≤
      (1 / (2542281481 / 80000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2542281481 / 80000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((21 / 800 : ℝ) - Real.pi * Real.exp (83 / 800 : ℝ)) ≤
      (2 / (2542281481 / 80000000 : ℝ) : ℝ) := by
    rw [show (21 / 800 : ℝ) - Real.pi * Real.exp (83 / 800 : ℝ) =
      -(Real.pi * Real.exp (83 / 800 : ℝ) - (21 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4361750848322959 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (4361750848322959 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell83_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (83 / 1600 : ℝ) (21 / 400 : ℝ)) :
    (4333554523 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17521515469 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell83_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell83_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell84_leftExp :
    (11107106103 / 10000000000 : ℝ) ≤ Real.exp (21 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (21 / 200 : ℝ) (1003286639193 / 1000000000000 : ℝ)
    (11107106103 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell84_rightExp :
    Real.exp (17 / 160 : ℝ) ≤ (2780249667 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (17 / 160 : ℝ) (250831457711 / 250000000000 : ℝ)
    (2780249667 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell84_denomUpper :
    Real.exp (8668787892099531 / 2500000000000000 : ℝ) ≤ (320569868119 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8668787892099531 / 2500000000000000 : ℝ) (139306088263 /
    125000000000 : ℝ) (320569868119 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell84_denomLower :
    (159536857981 / 5000000000 : ℝ) ≤ Real.exp (4328546334541997 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4328546334541997 / 1250000000000000 : ℝ) (557142898217 /
    500000000000 : ℝ) (159536857981 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell84_product_lower :
    (4361749459541997 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (21 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell84_leftExp
    (by norm_num : (0 : ℝ) ≤ (11107106103 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell84_product_upper :
    Real.pi * Real.exp (17 / 160 : ℝ) ≤ (8734412892099531 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell84_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell84_endpointLower :
    (8661837161 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (21 / 400 : ℝ) (17 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4361749459541997 / 1250000000000000 : ℝ) (Real.pi * Real.exp (21 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell84_product_lower
  have hD : Real.exp (Real.pi * Real.exp (17 / 160 : ℝ) - (21 / 800 : ℝ)) ≤
      (320569868119 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell84_denomUpper
    linarith [hpThetaJensenCell84_product_upper]
  have hi : (1 / (320569868119 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (17 / 160 : ℝ) - (21 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (320569868119 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (320569868119 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((21 / 800 : ℝ) - Real.pi * Real.exp (17 / 160 : ℝ)) := by
    rw [show (21 / 800 : ℝ) - Real.pi * Real.exp (17 / 160 : ℝ) =
      -(Real.pi * Real.exp (17 / 160 : ℝ) - (21 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (21 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (21 / 200 : ℝ)) := by
    have h := hpThetaJensenCell84_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (320569868119 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell84_endpointUpper :
    hpThetaJensenKernelEndpointUpper (21 / 400 : ℝ) (17 / 320 : ℝ) ≤ (17510917077 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (17 / 160 : ℝ)) (8734412892099531 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (17 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell84_product_upper
  have hD : (159536857981 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (21 / 200 : ℝ) - (17 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell84_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell84_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (21 / 200 : ℝ) - (17 / 640 : ℝ)) ≤
      (1 / (159536857981 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (159536857981 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((17 / 640 : ℝ) - Real.pi * Real.exp (21 / 200 : ℝ)) ≤
      (2 / (159536857981 / 5000000000 : ℝ) : ℝ) := by
    rw [show (17 / 640 : ℝ) - Real.pi * Real.exp (21 / 200 : ℝ) =
      -(Real.pi * Real.exp (21 / 200 : ℝ) - (17 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8734412892099531 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (8734412892099531 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell84_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (21 / 400 : ℝ) (17 / 320 : ℝ)) :
    (8661837161 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17510917077 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell84_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell84_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell85_leftExp :
    (11120998667 / 10000000000 : ℝ) ≤ Real.exp (17 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (17 / 160 : ℝ) (1003325830843 / 1000000000000 : ℝ)
    (11120998667 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell85_rightExp :
    Real.exp (43 / 400 : ℝ) ≤ (173982947 / 156250000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (43 / 400 : ℝ) (40134600961 / 40000000000 : ℝ)
    (173982947 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell85_denomUpper :
    Real.exp (542433217789571 / 156250000000000 : ℝ) ≤ (321873202473 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (542433217789571 / 156250000000000 : ℝ) (557295010741 /
    500000000000 : ℝ) (321873202473 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell85_denomLower :
    (40046152269 / 1250000000 : ℝ) ≤ Real.exp (4333611305532233 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4333611305532233 / 1250000000000000 : ℝ) (557213450499 /
    500000000000 : ℝ) (40046152269 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell85_product_lower :
    (4367205055532233 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (17 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell85_leftExp
    (by norm_num : (0 : ℝ) ≤ (11120998667 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell85_product_upper :
    Real.pi * Real.exp (43 / 400 : ℝ) ≤ (546583608414571 / 156250000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell85_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell85_endpointLower :
    (8656503341 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (17 / 320 : ℝ) (43 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4367205055532233 / 1250000000000000 : ℝ) (Real.pi * Real.exp (17 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell85_product_lower
  have hD : Real.exp (Real.pi * Real.exp (43 / 400 : ℝ) - (17 / 640 : ℝ)) ≤
      (321873202473 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell85_denomUpper
    linarith [hpThetaJensenCell85_product_upper]
  have hi : (1 / (321873202473 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (43 / 400 : ℝ) - (17 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (321873202473 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (321873202473 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((17 / 640 : ℝ) - Real.pi * Real.exp (43 / 400 : ℝ)) := by
    rw [show (17 / 640 : ℝ) - Real.pi * Real.exp (43 / 400 : ℝ) =
      -(Real.pi * Real.exp (43 / 400 : ℝ) - (17 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (17 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (17 / 160 : ℝ)) := by
    have h := hpThetaJensenCell85_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (321873202473 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell85_endpointUpper :
    hpThetaJensenKernelEndpointUpper (17 / 320 : ℝ) (43 / 800 : ℝ) ≤ (17500193629 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (43 / 400 : ℝ)) (546583608414571 / 156250000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (43 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell85_product_upper
  have hD : (40046152269 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (17 / 160 : ℝ) - (43 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell85_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell85_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (17 / 160 : ℝ) - (43 / 1600 : ℝ)) ≤
      (1 / (40046152269 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (40046152269 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((43 / 1600 : ℝ) - Real.pi * Real.exp (17 / 160 : ℝ)) ≤
      (2 / (40046152269 / 1250000000 : ℝ) : ℝ) := by
    rw [show (43 / 1600 : ℝ) - Real.pi * Real.exp (17 / 160 : ℝ) =
      -(Real.pi * Real.exp (17 / 160 : ℝ) - (43 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (546583608414571 / 156250000000000 : ℝ) ^ 2 - 6 *
      (546583608414571 / 156250000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell85_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (17 / 320 : ℝ) (43 / 800 : ℝ)) :
    (8656503341 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17500193629 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell85_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell85_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell86_leftExp :
    (11134908607 / 10000000000 : ℝ) ≤ Real.exp (43 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (43 / 400 : ℝ) (125420628003 / 125000000000 : ℝ)
    (11134908607 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell86_rightExp :
    Real.exp (87 / 800 : ℝ) ≤ (11148835947 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (87 / 800 : ℝ) (62712763671 / 62500000000 : ℝ)
    (11148835947 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell86_denomUpper :
    Real.exp (34756354969243571 / 10000000000000000 : ℝ) ≤ (323183602309 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (34756354969243571 / 10000000000000000 : ℝ) (139341443149
    / 125000000000 : ℝ) (323183602309 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell86_denomLower :
    (321671736283 / 10000000000 : ℝ) ≤ Real.exp (4338683100060293 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4338683100060293 / 1250000000000000 : ℝ) (1114568213563
    / 1000000000000 : ℝ) (321671736283 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell86_product_lower :
    (4372667475060293 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (43 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell86_leftExp
    (by norm_num : (0 : ℝ) ≤ (11134908607 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell86_product_upper :
    Real.pi * Real.exp (87 / 800 : ℝ) ≤ (35025104969243571 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell86_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell86_endpointLower :
    (1730221539 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (43 / 800 : ℝ) (87 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4372667475060293 / 1250000000000000 : ℝ) (Real.pi * Real.exp (43 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell86_product_lower
  have hD : Real.exp (Real.pi * Real.exp (87 / 800 : ℝ) - (43 / 1600 : ℝ)) ≤
      (323183602309 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell86_denomUpper
    linarith [hpThetaJensenCell86_product_upper]
  have hi : (1 / (323183602309 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (87 / 800 : ℝ) - (43 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (323183602309 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (323183602309 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((43 / 1600 : ℝ) - Real.pi * Real.exp (87 / 800 : ℝ)) := by
    rw [show (43 / 1600 : ℝ) - Real.pi * Real.exp (87 / 800 : ℝ) =
      -(Real.pi * Real.exp (87 / 800 : ℝ) - (43 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (43 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (43 / 400 : ℝ)) := by
    have h := hpThetaJensenCell86_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (323183602309 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell86_endpointUpper :
    hpThetaJensenKernelEndpointUpper (43 / 800 : ℝ) (87 / 1600 : ℝ) ≤ (4372336341 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (87 / 800 : ℝ)) (35025104969243571 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (87 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell86_product_upper
  have hD : (321671736283 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (43 / 400 : ℝ) - (87 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell86_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell86_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (43 / 400 : ℝ) - (87 / 3200 : ℝ)) ≤
      (1 / (321671736283 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (321671736283 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((87 / 3200 : ℝ) - Real.pi * Real.exp (43 / 400 : ℝ)) ≤
      (2 / (321671736283 / 10000000000 : ℝ) : ℝ) := by
    rw [show (87 / 3200 : ℝ) - Real.pi * Real.exp (43 / 400 : ℝ) =
      -(Real.pi * Real.exp (43 / 400 : ℝ) - (87 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (35025104969243571 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (35025104969243571 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell86_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (43 / 800 : ℝ) (87 / 1600 : ℝ)) :
    (1730221539 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4372336341 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell86_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell86_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell87_leftExp :
    (2229767189 / 2000000000 : ℝ) ≤ Real.exp (87 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (87 / 800 : ℝ) (200680843747 / 200000000000 : ℝ)
    (2229767189 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell87_rightExp :
    Real.exp (11 / 100 : ℝ) ≤ (2232556141 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11 / 100 : ℝ) (1003443414979 / 1000000000000 : ℝ)
    (2232556141 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell87_denomUpper :
    Real.exp (6959407744672613 / 2000000000000000 : ℝ) ≤ (162250556389 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (6959407744672613 / 2000000000000000 : ℝ) (1114873277527
    / 1000000000000 : ℝ) (162250556389 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell87_denomLower :
    (32298131537 / 1000000000 : ℝ) ≤ Real.exp (868752345353111 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (868752345353111 / 250000000000000 : ℝ) (222941946889 /
    200000000000 : ℝ) (32298131537 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell87_product_lower :
    (875627345353111 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (87 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell87_leftExp
    (by norm_num : (0 : ℝ) ≤ (2229767189 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell87_product_upper :
    Real.pi * Real.exp (11 / 100 : ℝ) ≤ (7013782744672613 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell87_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell87_endpointLower :
    (17291300691 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (87 / 1600 : ℝ) (11 / 200 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (875627345353111 / 250000000000000 : ℝ) (Real.pi * Real.exp (87 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell87_product_lower
  have hD : Real.exp (Real.pi * Real.exp (11 / 100 : ℝ) - (87 / 3200 : ℝ)) ≤
      (162250556389 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell87_denomUpper
    linarith [hpThetaJensenCell87_product_upper]
  have hi : (1 / (162250556389 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (11 / 100 : ℝ) - (87 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (162250556389 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (162250556389 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((87 / 3200 : ℝ) - Real.pi * Real.exp (11 / 100 : ℝ)) := by
    rw [show (87 / 3200 : ℝ) - Real.pi * Real.exp (11 / 100 : ℝ) =
      -(Real.pi * Real.exp (11 / 100 : ℝ) - (87 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (87 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (87 / 800 : ℝ)) := by
    have h := hpThetaJensenCell87_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (162250556389 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell87_endpointUpper :
    hpThetaJensenKernelEndpointUpper (87 / 1600 : ℝ) (11 / 200 : ℝ) ≤ (8739186253 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (11 / 100 : ℝ)) (7013782744672613 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (11 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell87_product_upper
  have hD : (32298131537 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (87 / 800 : ℝ) - (11 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell87_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell87_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (87 / 800 : ℝ) - (11 / 400 : ℝ)) ≤
      (1 / (32298131537 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (32298131537 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((11 / 400 : ℝ) - Real.pi * Real.exp (87 / 800 : ℝ)) ≤
      (2 / (32298131537 / 1000000000 : ℝ) : ℝ) := by
    rw [show (11 / 400 : ℝ) - Real.pi * Real.exp (87 / 800 : ℝ) =
      -(Real.pi * Real.exp (87 / 800 : ℝ) - (11 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (7013782744672613 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (7013782744672613 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell87_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (87 / 1600 : ℝ) (11 / 200 : ℝ)) :
    (17291300691 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8739186253 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell87_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell87_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell88_leftExp :
    (348836897 / 312500000 : ℝ) ≤ Real.exp (11 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11 / 100 : ℝ) (501721707489 / 500000000000 : ℝ)
    (348836897 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell88_rightExp :
    Real.exp (89 / 800 : ℝ) ≤ (5588371453 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (89 / 800 : ℝ) (1003482612753 / 1000000000000 : ℝ)
    (5588371453 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell88_denomUpper :
    Real.exp (17418888638144629 / 5000000000000000 : ℝ) ≤ (40728222471 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (17418888638144629 / 5000000000000000 : ℝ) (139376902353
    / 125000000000 : ℝ) (40728222471 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell88_denomLower :
    (324298000831 / 10000000000 : ℝ) ≤ Real.exp (135901474833753 / 39062500000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (135901474833753 / 39062500000000 : ℝ) (1114851463969 /
    1000000000000 : ℝ) (324298000831 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell88_product_lower :
    (136987900615003 / 39062500000000 : ℝ) ≤ Real.pi * Real.exp (11 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell88_leftExp
    (by norm_num : (0 : ℝ) ≤ (348836897 / 312500000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell88_product_upper :
    Real.pi * Real.exp (89 / 800 : ℝ) ≤ (17556388638144629 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell88_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell88_endpointLower :
    (17280262813 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (11 / 200 : ℝ) (89 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (136987900615003 / 39062500000000 : ℝ) (Real.pi * Real.exp (11 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell88_product_lower
  have hD : Real.exp (Real.pi * Real.exp (89 / 800 : ℝ) - (11 / 400 : ℝ)) ≤
      (40728222471 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell88_denomUpper
    linarith [hpThetaJensenCell88_product_upper]
  have hi : (1 / (40728222471 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (89 / 800 : ℝ) - (11 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (40728222471 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (40728222471 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((11 / 400 : ℝ) - Real.pi * Real.exp (89 / 800 : ℝ)) := by
    rw [show (11 / 400 : ℝ) - Real.pi * Real.exp (89 / 800 : ℝ) =
      -(Real.pi * Real.exp (89 / 800 : ℝ) - (11 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (11 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (11 / 100 : ℝ)) := by
    have h := hpThetaJensenCell88_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (40728222471 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell88_endpointUpper :
    hpThetaJensenKernelEndpointUpper (11 / 200 : ℝ) (89 / 1600 : ℝ) ≤ (8733637647 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (89 / 800 : ℝ)) (17556388638144629 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (89 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell88_product_upper
  have hD : (324298000831 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (11 / 100 : ℝ) - (89 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell88_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell88_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (11 / 100 : ℝ) - (89 / 3200 : ℝ)) ≤
      (1 / (324298000831 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (324298000831 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((89 / 3200 : ℝ) - Real.pi * Real.exp (11 / 100 : ℝ)) ≤
      (2 / (324298000831 / 10000000000 : ℝ) : ℝ) := by
    rw [show (89 / 3200 : ℝ) - Real.pi * Real.exp (11 / 100 : ℝ) =
      -(Real.pi * Real.exp (11 / 100 : ℝ) - (89 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (17556388638144629 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (17556388638144629 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell88_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (11 / 200 : ℝ) (89 / 1600 : ℝ)) :
    (17280262813 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8733637647 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell88_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell88_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell89_leftExp :
    (1397092863 / 1250000000 : ℝ) ≤ Real.exp (89 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (89 / 800 : ℝ) (62717663297 / 62500000000 : ℝ)
    (1397092863 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell89_rightExp :
    Real.exp (9 / 80 : ℝ) ≤ (1119072257 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9 / 80 : ℝ) (501760906029 / 500000000000 : ℝ)
    (1119072257 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell89_denomUpper :
    Real.exp (3487857069085401 / 1000000000000000 : ℝ) ≤ (327157649113 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3487857069085401 / 1000000000000000 : ℝ) (1115157369379
    / 1000000000000 : ℝ) (327157649113 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell89_denomLower :
    (65124367627 / 2000000000 : ℝ) ≤ Real.exp (544242438957237 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (544242438957237 / 156250000000000 : ℝ) (111499340243 /
    100000000000 : ℝ) (65124367627 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell89_product_lower :
    (548636970207237 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (89 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell89_leftExp
    (by norm_num : (0 : ℝ) ≤ (1397092863 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell89_product_upper :
    Real.pi * Real.exp (9 / 80 : ℝ) ≤ (3515669569085401 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell89_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell89_endpointLower :
    (17269101993 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (89 / 1600 : ℝ) (9 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (548636970207237 / 156250000000000 : ℝ) (Real.pi * Real.exp (89 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell89_product_lower
  have hD : Real.exp (Real.pi * Real.exp (9 / 80 : ℝ) - (89 / 3200 : ℝ)) ≤
      (327157649113 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell89_denomUpper
    linarith [hpThetaJensenCell89_product_upper]
  have hi : (1 / (327157649113 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (9 / 80 : ℝ) - (89 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (327157649113 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (327157649113 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((89 / 3200 : ℝ) - Real.pi * Real.exp (9 / 80 : ℝ)) := by
    rw [show (89 / 3200 : ℝ) - Real.pi * Real.exp (9 / 80 : ℝ) =
      -(Real.pi * Real.exp (9 / 80 : ℝ) - (89 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (89 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (89 / 800 : ℝ)) := by
    have h := hpThetaJensenCell89_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (327157649113 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell89_endpointUpper :
    hpThetaJensenKernelEndpointUpper (89 / 1600 : ℝ) (9 / 160 : ℝ) ≤ (3491210793 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (9 / 80 : ℝ)) (3515669569085401 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (9 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell89_product_upper
  have hD : (65124367627 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (89 / 800 : ℝ) - (9 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell89_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell89_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (89 / 800 : ℝ) - (9 / 320 : ℝ)) ≤
      (1 / (65124367627 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (65124367627 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((9 / 320 : ℝ) - Real.pi * Real.exp (89 / 800 : ℝ)) ≤
      (2 / (65124367627 / 2000000000 : ℝ) : ℝ) := by
    rw [show (9 / 320 : ℝ) - Real.pi * Real.exp (89 / 800 : ℝ) =
      -(Real.pi * Real.exp (89 / 800 : ℝ) - (9 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (3515669569085401 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (3515669569085401 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell89_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (89 / 1600 : ℝ) (9 / 160 : ℝ)) :
    (17269101993 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3491210793 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell89_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell89_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell90_leftExp :
    (1398840321 / 1250000000 : ℝ) ≤ Real.exp (9 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9 / 80 : ℝ) (1003521812057 / 1000000000000 : ℝ)
    (1398840321 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell90_rightExp :
    Real.exp (91 / 800 : ℝ) ≤ (11204719719 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (91 / 800 : ℝ) (200712202579 / 200000000000 : ℝ)
    (11204719719 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell90_denomUpper :
    Real.exp (34919419036172367 / 10000000000000000 : ℝ) ≤ (65699353429 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (34919419036172367 / 10000000000000000 : ℝ) (557649864753
    / 500000000000 : ℝ) (65699353429 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell90_denomLower :
    (326952873367 / 10000000000 : ℝ) ≤ Real.exp (544879835841379 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (544879835841379 / 156250000000000 : ℝ) (557567775077 /
    500000000000 : ℝ) (326952873367 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell90_product_lower :
    (549323195216379 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (9 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell90_leftExp
    (by norm_num : (0 : ℝ) ≤ (1398840321 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell90_product_upper :
    Real.pi * Real.exp (91 / 800 : ℝ) ≤ (35200669036172367 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell90_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell90_endpointLower :
    (4314454619 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (9 / 160 : ℝ) (91 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (549323195216379 / 156250000000000 : ℝ) (Real.pi * Real.exp (9 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell90_product_lower
  have hD : Real.exp (Real.pi * Real.exp (91 / 800 : ℝ) - (9 / 320 : ℝ)) ≤
      (65699353429 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell90_denomUpper
    linarith [hpThetaJensenCell90_product_upper]
  have hi : (1 / (65699353429 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (91 / 800 : ℝ) - (9 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (65699353429 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (65699353429 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((9 / 320 : ℝ) - Real.pi * Real.exp (91 / 800 : ℝ)) := by
    rw [show (9 / 320 : ℝ) - Real.pi * Real.exp (91 / 800 : ℝ) =
      -(Real.pi * Real.exp (91 / 800 : ℝ) - (9 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (9 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (9 / 80 : ℝ)) := by
    have h := hpThetaJensenCell90_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (65699353429 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell90_endpointUpper :
    hpThetaJensenKernelEndpointUpper (9 / 160 : ℝ) (91 / 1600 : ℝ) ≤ (8722354377 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (91 / 800 : ℝ)) (35200669036172367 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (91 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell90_product_upper
  have hD : (326952873367 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (9 / 80 : ℝ) - (91 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell90_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell90_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (9 / 80 : ℝ) - (91 / 3200 : ℝ)) ≤
      (1 / (326952873367 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (326952873367 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((91 / 3200 : ℝ) - Real.pi * Real.exp (9 / 80 : ℝ)) ≤
      (2 / (326952873367 / 10000000000 : ℝ) : ℝ) := by
    rw [show (91 / 3200 : ℝ) - Real.pi * Real.exp (9 / 80 : ℝ) =
      -(Real.pi * Real.exp (9 / 80 : ℝ) - (91 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (35200669036172367 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (35200669036172367 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell90_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (9 / 160 : ℝ) (91 / 1600 : ℝ)) :
    (4314454619 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8722354377 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell90_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell90_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell91_leftExp :
    (5602359859 / 5000000000 : ℝ) ≤ Real.exp (91 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (91 / 800 : ℝ) (501780506447 / 500000000000 : ℝ)
    (5602359859 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell91_rightExp :
    Real.exp (23 / 200 : ℝ) ≤ (11218734377 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (23 / 200 : ℝ) (1003600215263 / 1000000000000 : ℝ)
    (11218734377 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell91_denomUpper :
    Real.exp (34960322387642561 / 10000000000000000 : ℝ) ≤ (329843180789 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (34960322387642561 / 10000000000000000 : ℝ) (557721149773
    / 500000000000 : ℝ) (329843180789 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell91_denomLower :
    (328291152859 / 10000000000 : ℝ) ≤ Real.exp (2182072364269441 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2182072364269441 / 625000000000000 : ℝ) (557638953729 /
    500000000000 : ℝ) (328291152859 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell91_product_lower :
    (2200041114269441 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (91 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell91_leftExp
    (by norm_num : (0 : ℝ) ≤ (5602359859 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell91_product_upper :
    Real.pi * Real.exp (23 / 200 : ℝ) ≤ (35244697387642561 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell91_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell91_endpointLower :
    (1724641249 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (91 / 1600 : ℝ) (23 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2200041114269441 / 625000000000000 : ℝ) (Real.pi * Real.exp (91 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell91_product_lower
  have hD : Real.exp (Real.pi * Real.exp (23 / 200 : ℝ) - (91 / 3200 : ℝ)) ≤
      (329843180789 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell91_denomUpper
    linarith [hpThetaJensenCell91_product_upper]
  have hi : (1 / (329843180789 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (23 / 200 : ℝ) - (91 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (329843180789 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (329843180789 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((91 / 3200 : ℝ) - Real.pi * Real.exp (23 / 200 : ℝ)) := by
    rw [show (91 / 3200 : ℝ) - Real.pi * Real.exp (23 / 200 : ℝ) =
      -(Real.pi * Real.exp (23 / 200 : ℝ) - (91 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (91 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (91 / 800 : ℝ)) := by
    have h := hpThetaJensenCell91_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (329843180789 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell91_endpointUpper :
    hpThetaJensenKernelEndpointUpper (91 / 1600 : ℝ) (23 / 400 : ℝ) ≤ (17433239909 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (23 / 200 : ℝ)) (35244697387642561 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (23 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell91_product_upper
  have hD : (328291152859 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (91 / 800 : ℝ) - (23 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell91_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell91_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (91 / 800 : ℝ) - (23 / 800 : ℝ)) ≤
      (1 / (328291152859 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (328291152859 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((23 / 800 : ℝ) - Real.pi * Real.exp (91 / 800 : ℝ)) ≤
      (2 / (328291152859 / 10000000000 : ℝ) : ℝ) := by
    rw [show (23 / 800 : ℝ) - Real.pi * Real.exp (91 / 800 : ℝ) =
      -(Real.pi * Real.exp (91 / 800 : ℝ) - (23 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (35244697387642561 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (35244697387642561 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell91_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (91 / 1600 : ℝ) (23 / 400 : ℝ)) :
    (1724641249 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17433239909 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell91_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell91_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell92_leftExp :
    (717999 / 640000 : ℝ) ≤ Real.exp (23 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (23 / 200 : ℝ) (501800107631 / 500000000000 : ℝ) (717999
    / 640000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell92_rightExp :
    Real.exp (93 / 800 : ℝ) ≤ (11232766563 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (93 / 800 : ℝ) (501819709581 / 500000000000 : ℝ)
    (11232766563 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell92_denomUpper :
    Real.exp (35001280804954859 / 10000000000000000 : ℝ) ≤ (331196936747 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (35001280804954859 / 10000000000000000 : ℝ)
    (1115585079781 / 1000000000000 : ℝ) (331196936747 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell92_denomLower :
    (329636723177 / 10000000000 : ℝ) ≤ Real.exp (279632489301 / 80000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (279632489301 / 80000000000 : ℝ) (139427559331 /
    125000000000 : ℝ) (329636723177 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell92_product_lower :
    (281957489301 / 80000000000 : ℝ) ≤ Real.pi * Real.exp (23 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell92_leftExp
    (by norm_num : (0 : ℝ) ≤ (717999 / 640000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell92_product_upper :
    Real.pi * Real.exp (93 / 800 : ℝ) ≤ (35288780804954859 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell92_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell92_endpointLower :
    (1723488429 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (23 / 400 : ℝ) (93 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (281957489301 / 80000000000 : ℝ) (Real.pi * Real.exp (23 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell92_product_lower
  have hD : Real.exp (Real.pi * Real.exp (93 / 800 : ℝ) - (23 / 800 : ℝ)) ≤
      (331196936747 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell92_denomUpper
    linarith [hpThetaJensenCell92_product_upper]
  have hi : (1 / (331196936747 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (93 / 800 : ℝ) - (23 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (331196936747 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (331196936747 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((23 / 800 : ℝ) - Real.pi * Real.exp (93 / 800 : ℝ)) := by
    rw [show (23 / 800 : ℝ) - Real.pi * Real.exp (93 / 800 : ℝ) =
      -(Real.pi * Real.exp (93 / 800 : ℝ) - (23 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (23 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (23 / 200 : ℝ)) := by
    have h := hpThetaJensenCell92_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (331196936747 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell92_endpointUpper :
    hpThetaJensenKernelEndpointUpper (23 / 400 : ℝ) (93 / 1600 : ℝ) ≤ (8710823833 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (93 / 800 : ℝ)) (35288780804954859 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (93 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell92_product_upper
  have hD : (329636723177 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (23 / 200 : ℝ) - (93 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell92_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell92_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (23 / 200 : ℝ) - (93 / 3200 : ℝ)) ≤
      (1 / (329636723177 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (329636723177 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((93 / 3200 : ℝ) - Real.pi * Real.exp (23 / 200 : ℝ)) ≤
      (2 / (329636723177 / 10000000000 : ℝ) : ℝ) := by
    rw [show (93 / 3200 : ℝ) - Real.pi * Real.exp (23 / 200 : ℝ) =
      -(Real.pi * Real.exp (23 / 200 : ℝ) - (93 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (35288780804954859 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (35288780804954859 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell92_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (23 / 400 : ℝ) (93 / 1600 : ℝ)) :
    (1723488429 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8710823833 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell92_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell92_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell93_leftExp :
    (11232766561 / 10000000000 : ℝ) ≤ Real.exp (93 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (93 / 800 : ℝ) (1003639419161 / 1000000000000 : ℝ)
    (11232766561 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell93_rightExp :
    Real.exp (47 / 400 : ℝ) ≤ (112468163 / 100000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (47 / 400 : ℝ) (62729914037 / 62500000000 : ℝ)
    (112468163 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell93_denomUpper :
    Real.exp (350422943603659 / 100000000000000 : ℝ) ≤ (166279041249 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (350422943603659 / 100000000000000 : ℝ) (1115728070539 /
    1000000000000 : ℝ) (166279041249 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell93_denomLower :
    (82747407829 / 2500000000 : ℝ) ≤ Real.exp (4374377445738139 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4374377445738139 / 1250000000000000 : ℝ) (27889081301 /
    25000000000 : ℝ) (82747407829 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell93_product_lower :
    (4411096195738139 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (93 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell93_leftExp
    (by norm_num : (0 : ℝ) ≤ (11232766561 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell93_product_upper :
    Real.pi * Real.exp (47 / 400 : ℝ) ≤ (353329193603659 / 100000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell93_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell93_endpointLower :
    (3444646823 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (93 / 1600 : ℝ) (47 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4411096195738139 / 1250000000000000 : ℝ) (Real.pi * Real.exp (93 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell93_product_lower
  have hD : Real.exp (Real.pi * Real.exp (47 / 400 : ℝ) - (93 / 3200 : ℝ)) ≤
      (166279041249 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell93_denomUpper
    linarith [hpThetaJensenCell93_product_upper]
  have hi : (1 / (166279041249 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (47 / 400 : ℝ) - (93 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (166279041249 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (166279041249 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((93 / 3200 : ℝ) - Real.pi * Real.exp (47 / 400 : ℝ)) := by
    rw [show (93 / 3200 : ℝ) - Real.pi * Real.exp (47 / 400 : ℝ) =
      -(Real.pi * Real.exp (47 / 400 : ℝ) - (93 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (93 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (93 / 800 : ℝ)) := by
    have h := hpThetaJensenCell93_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (166279041249 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell93_endpointUpper :
    hpThetaJensenKernelEndpointUpper (93 / 1600 : ℝ) (47 / 800 : ℝ) ≤ (8704966137 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (47 / 400 : ℝ)) (353329193603659 / 100000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (47 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell93_product_upper
  have hD : (82747407829 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (93 / 800 : ℝ) - (47 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell93_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell93_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (93 / 800 : ℝ) - (47 / 1600 : ℝ)) ≤
      (1 / (82747407829 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (82747407829 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((47 / 1600 : ℝ) - Real.pi * Real.exp (93 / 800 : ℝ)) ≤
      (2 / (82747407829 / 2500000000 : ℝ) : ℝ) := by
    rw [show (47 / 1600 : ℝ) - Real.pi * Real.exp (93 / 800 : ℝ) =
      -(Real.pi * Real.exp (93 / 800 : ℝ) - (47 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (353329193603659 / 100000000000000 : ℝ) ^ 2 - 6 *
      (353329193603659 / 100000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell93_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (93 / 1600 : ℝ) (47 / 800 : ℝ)) :
    (3444646823 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8704966137 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell93_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell93_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell94_leftExp :
    (11246816299 / 10000000000 : ℝ) ≤ Real.exp (47 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (47 / 400 : ℝ) (1003678624591 / 1000000000000 : ℝ)
    (11246816299 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell94_rightExp :
    Real.exp (19 / 160 : ℝ) ≤ (11260883611 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (19 / 160 : ℝ) (501858915777 / 500000000000 : ℝ)
    (11260883611 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell94_denomUpper :
    Real.exp (35083363126132323 / 10000000000000000 : ℝ) ≤ (333926665873 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (35083363126132323 / 10000000000000000 : ℝ)
    (1115871272149 / 1000000000000 : ℝ) (333926665873 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell94_denomLower :
    (83087481183 / 2500000000 : ℝ) ≤ Real.exp (4379504138801001 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4379504138801001 / 1250000000000000 : ℝ) (1115706239963
    / 1000000000000 : ℝ) (83087481183 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell94_product_lower :
    (4416613513801001 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (47 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell94_leftExp
    (by norm_num : (0 : ℝ) ≤ (11246816299 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell94_product_upper :
    Real.pi * Real.exp (19 / 160 : ℝ) ≤ (35377113126132323 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell94_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell94_endpointLower :
    (17211462211 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (47 / 800 : ℝ) (19 / 320 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4416613513801001 / 1250000000000000 : ℝ) (Real.pi * Real.exp (47 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell94_product_lower
  have hD : Real.exp (Real.pi * Real.exp (19 / 160 : ℝ) - (47 / 1600 : ℝ)) ≤
      (333926665873 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell94_denomUpper
    linarith [hpThetaJensenCell94_product_upper]
  have hi : (1 / (333926665873 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (19 / 160 : ℝ) - (47 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (333926665873 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (333926665873 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((47 / 1600 : ℝ) - Real.pi * Real.exp (19 / 160 : ℝ)) := by
    rw [show (47 / 1600 : ℝ) - Real.pi * Real.exp (19 / 160 : ℝ) =
      -(Real.pi * Real.exp (19 / 160 : ℝ) - (47 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (47 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (47 / 400 : ℝ)) := by
    have h := hpThetaJensenCell94_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (333926665873 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell94_endpointUpper :
    hpThetaJensenKernelEndpointUpper (47 / 800 : ℝ) (19 / 320 : ℝ) ≤ (17398093979 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (19 / 160 : ℝ)) (35377113126132323 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (19 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell94_product_upper
  have hD : (83087481183 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (47 / 400 : ℝ) - (19 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell94_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell94_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (47 / 400 : ℝ) - (19 / 640 : ℝ)) ≤
      (1 / (83087481183 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (83087481183 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((19 / 640 : ℝ) - Real.pi * Real.exp (47 / 400 : ℝ)) ≤
      (2 / (83087481183 / 2500000000 : ℝ) : ℝ) := by
    rw [show (19 / 640 : ℝ) - Real.pi * Real.exp (47 / 400 : ℝ) =
      -(Real.pi * Real.exp (47 / 400 : ℝ) - (19 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (35377113126132323 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (35377113126132323 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell94_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (47 / 800 : ℝ) (19 / 320 : ℝ)) :
    (17211462211 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17398093979 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell94_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell94_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell95_leftExp :
    (11260883609 / 10000000000 : ℝ) ≤ Real.exp (19 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (19 / 160 : ℝ) (1003717831553 / 1000000000000 : ℝ)
    (11260883609 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell95_rightExp :
    Real.exp (3 / 25 : ℝ) ≤ (11274968517 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3 / 25 : ℝ) (62734815003 / 62500000000 : ℝ)
    (11274968517 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell95_denomUpper :
    Real.exp (35124487168227581 / 10000000000000000 : ℝ) ≤ (335302734839 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (35124487168227581 / 10000000000000000 : ℝ) (558007342459
    / 500000000000 : ℝ) (335302734839 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell95_denomLower :
    (20857353181 / 625000000 : ℝ) ≤ Real.exp (4384637732370691 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4384637732370691 / 1250000000000000 : ℝ) (1115849438711
    / 1000000000000 : ℝ) (20857353181 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell95_product_lower :
    (4422137732370691 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (19 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell95_leftExp
    (by norm_num : (0 : ℝ) ≤ (11260883609 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell95_product_upper :
    Real.pi * Real.exp (3 / 25 : ℝ) ≤ (35421362168227581 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell95_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell95_endpointLower :
    (17199568823 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (19 / 320 : ℝ) (3 / 50 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4422137732370691 / 1250000000000000 : ℝ) (Real.pi * Real.exp (19 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell95_product_lower
  have hD : Real.exp (Real.pi * Real.exp (3 / 25 : ℝ) - (19 / 640 : ℝ)) ≤
      (335302734839 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell95_denomUpper
    linarith [hpThetaJensenCell95_product_upper]
  have hi : (1 / (335302734839 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (3 / 25 : ℝ) - (19 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (335302734839 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (335302734839 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((19 / 640 : ℝ) - Real.pi * Real.exp (3 / 25 : ℝ)) := by
    rw [show (19 / 640 : ℝ) - Real.pi * Real.exp (3 / 25 : ℝ) =
      -(Real.pi * Real.exp (3 / 25 : ℝ) - (19 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (19 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (19 / 160 : ℝ)) := by
    have h := hpThetaJensenCell95_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (335302734839 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell95_endpointUpper :
    hpThetaJensenKernelEndpointUpper (19 / 320 : ℝ) (3 / 50 : ℝ) ≤ (17386133037 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (3 / 25 : ℝ)) (35421362168227581 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (3 / 50 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell95_product_upper
  have hD : (20857353181 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (19 / 160 : ℝ) - (3 / 100 : ℝ)) := by
    apply le_trans hpThetaJensenCell95_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell95_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (19 / 160 : ℝ) - (3 / 100 : ℝ)) ≤
      (1 / (20857353181 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (20857353181 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((3 / 100 : ℝ) - Real.pi * Real.exp (19 / 160 : ℝ)) ≤
      (2 / (20857353181 / 625000000 : ℝ) : ℝ) := by
    rw [show (3 / 100 : ℝ) - Real.pi * Real.exp (19 / 160 : ℝ) =
      -(Real.pi * Real.exp (19 / 160 : ℝ) - (3 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (35421362168227581 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (35421362168227581 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell95_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (19 / 320 : ℝ) (3 / 50 : ℝ)) :
    (17199568823 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17386133037 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell95_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell95_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell96_leftExp :
    (2254993703 / 2000000000 : ℝ) ≤ Real.exp (3 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3 / 25 : ℝ) (1003757040047 / 1000000000000 : ℝ)
    (2254993703 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell96_rightExp :
    Real.exp (97 / 800 : ℝ) ≤ (11289071039 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (97 / 800 : ℝ) (1003796250073 / 1000000000000 : ℝ)
    (11289071039 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell96_denomUpper :
    Real.exp (35165666552625127 / 10000000000000000 : ℝ) ≤ (336686337703 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (35165666552625127 / 10000000000000000 : ℝ) (34879947161
    / 31250000000 : ℝ) (336686337703 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell96_denomLower :
    (335092858069 / 10000000000 : ℝ) ≤ Real.exp (877955647174397 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (877955647174397 / 250000000000000 : ℝ) (8927942789 /
    8000000000 : ℝ) (335092858069 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell96_product_lower :
    (885533772174397 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (3 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell96_leftExp
    (by norm_num : (0 : ℝ) ≤ (2254993703 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell96_product_upper :
    Real.pi * Real.exp (97 / 800 : ℝ) ≤ (35465666552625127 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell96_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell96_endpointLower :
    (3437510843 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (3 / 50 : ℝ) (97 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (885533772174397 / 250000000000000 : ℝ) (Real.pi * Real.exp (3 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell96_product_lower
  have hD : Real.exp (Real.pi * Real.exp (97 / 800 : ℝ) - (3 / 100 : ℝ)) ≤
      (336686337703 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell96_denomUpper
    linarith [hpThetaJensenCell96_product_upper]
  have hi : (1 / (336686337703 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (97 / 800 : ℝ) - (3 / 100 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (336686337703 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (336686337703 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((3 / 100 : ℝ) - Real.pi * Real.exp (97 / 800 : ℝ)) := by
    rw [show (3 / 100 : ℝ) - Real.pi * Real.exp (97 / 800 : ℝ) =
      -(Real.pi * Real.exp (97 / 800 : ℝ) - (3 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (3 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (3 / 25 : ℝ)) := by
    have h := hpThetaJensenCell96_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (336686337703 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell96_endpointUpper :
    hpThetaJensenKernelEndpointUpper (3 / 50 : ℝ) (97 / 1600 : ℝ) ≤ (8687024841 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (97 / 800 : ℝ)) (35465666552625127 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (97 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell96_product_upper
  have hD : (335092858069 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (3 / 25 : ℝ) - (97 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell96_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell96_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (3 / 25 : ℝ) - (97 / 3200 : ℝ)) ≤
      (1 / (335092858069 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (335092858069 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((97 / 3200 : ℝ) - Real.pi * Real.exp (3 / 25 : ℝ)) ≤
      (2 / (335092858069 / 10000000000 : ℝ) : ℝ) := by
    rw [show (97 / 3200 : ℝ) - Real.pi * Real.exp (3 / 25 : ℝ) =
      -(Real.pi * Real.exp (3 / 25 : ℝ) - (97 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (35465666552625127 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (35465666552625127 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell96_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (3 / 50 : ℝ) (97 / 1600 : ℝ)) :
    (3437510843 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8687024841 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell96_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell96_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell97_leftExp :
    (5644535519 / 5000000000 : ℝ) ≤ Real.exp (97 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (97 / 800 : ℝ) (125474531259 / 125000000000 : ℝ)
    (5644535519 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell97_rightExp :
    Real.exp (49 / 400 : ℝ) ≤ (11303191201 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (49 / 400 : ℝ) (100383546163 / 100000000000 : ℝ)
    (11303191201 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell97_denomUpper :
    Real.exp (35206901354723193 / 10000000000000000 : ℝ) ≤ (169038761723 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (35206901354723193 / 10000000000000000 : ℝ)
    (1116302145191 / 1000000000000 : ℝ) (169038761723 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell97_denomLower :
    (84118898629 / 2500000000 : ℝ) ≤ Real.exp (2197462828775781 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2197462828775781 / 625000000000000 : ℝ) (111613647001 /
    100000000000 : ℝ) (84118898629 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell97_product_lower :
    (2216603453775781 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (97 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell97_leftExp
    (by norm_num : (0 : ℝ) ≤ (5644535519 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell97_product_upper :
    Real.pi * Real.exp (49 / 400 : ℝ) ≤ (35510026354723193 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell97_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell97_endpointLower :
    (137403349 / 80000000 : ℝ) ≤ hpThetaTraceEndpointLower (97 / 1600 : ℝ) (49 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2216603453775781 / 625000000000000 : ℝ) (Real.pi * Real.exp (97 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell97_product_lower
  have hD : Real.exp (Real.pi * Real.exp (49 / 400 : ℝ) - (97 / 3200 : ℝ)) ≤
      (169038761723 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell97_denomUpper
    linarith [hpThetaJensenCell97_product_upper]
  have hi : (1 / (169038761723 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (49 / 400 : ℝ) - (97 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (169038761723 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (169038761723 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((97 / 3200 : ℝ) - Real.pi * Real.exp (49 / 400 : ℝ)) := by
    rw [show (97 / 3200 : ℝ) - Real.pi * Real.exp (49 / 400 : ℝ) =
      -(Real.pi * Real.exp (49 / 400 : ℝ) - (97 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (97 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (97 / 800 : ℝ)) := by
    have h := hpThetaJensenCell97_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (169038761723 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell97_endpointUpper :
    hpThetaJensenKernelEndpointUpper (97 / 1600 : ℝ) (49 / 800 : ℝ) ≤ (17361844183 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (49 / 400 : ℝ)) (35510026354723193 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (49 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell97_product_upper
  have hD : (84118898629 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (97 / 800 : ℝ) - (49 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell97_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell97_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (97 / 800 : ℝ) - (49 / 1600 : ℝ)) ≤
      (1 / (84118898629 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (84118898629 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((49 / 1600 : ℝ) - Real.pi * Real.exp (97 / 800 : ℝ)) ≤
      (2 / (84118898629 / 2500000000 : ℝ) : ℝ) := by
    rw [show (49 / 1600 : ℝ) - Real.pi * Real.exp (97 / 800 : ℝ) =
      -(Real.pi * Real.exp (97 / 800 : ℝ) - (49 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (35510026354723193 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (35510026354723193 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell97_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (97 / 1600 : ℝ) (49 / 800 : ℝ)) :
    (137403349 / 80000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17361844183 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell97_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell97_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell98_leftExp :
    (14128989 / 12500000 : ℝ) ≤ Real.exp (49 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (49 / 400 : ℝ) (1003835461629 / 1000000000000 : ℝ)
    (14128989 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell98_rightExp :
    Real.exp (99 / 800 : ℝ) ≤ (452693161 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (99 / 800 : ℝ) (501937337359 / 500000000000 : ℝ)
    (452693161 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell98_denomUpper :
    Real.exp (1409927665745473 / 400000000000000 : ℝ) ≤ (169738170599 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1409927665745473 / 400000000000000 : ℝ) (1116446193353 /
    1000000000000 : ℝ) (169738170599 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell98_denomLower :
    (337865908999 / 10000000000 : ℝ) ≤ Real.exp (5500100007561 / 1562500000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5500100007561 / 1562500000000 : ℝ) (558140151593 /
    500000000000 : ℝ) (337865908999 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell98_product_lower :
    (5548439851311 / 1562500000000 : ℝ) ≤ Real.pi * Real.exp (49 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell98_leftExp
    (by norm_num : (0 : ℝ) ≤ (14128989 / 12500000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell98_product_upper :
    Real.pi * Real.exp (99 / 800 : ℝ) ≤ (1422177665745473 / 400000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell98_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell98_endpointLower :
    (17163162309 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (49 / 800 : ℝ) (99 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5548439851311 / 1562500000000 : ℝ) (Real.pi * Real.exp (49 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell98_product_lower
  have hD : Real.exp (Real.pi * Real.exp (99 / 800 : ℝ) - (49 / 1600 : ℝ)) ≤
      (169738170599 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell98_denomUpper
    linarith [hpThetaJensenCell98_product_upper]
  have hi : (1 / (169738170599 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (99 / 800 : ℝ) - (49 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (169738170599 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (169738170599 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((49 / 1600 : ℝ) - Real.pi * Real.exp (99 / 800 : ℝ)) := by
    rw [show (49 / 1600 : ℝ) - Real.pi * Real.exp (99 / 800 : ℝ) =
      -(Real.pi * Real.exp (99 / 800 : ℝ) - (49 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (49 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (49 / 400 : ℝ)) := by
    have h := hpThetaJensenCell98_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (169738170599 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell98_endpointUpper :
    hpThetaJensenKernelEndpointUpper (49 / 800 : ℝ) (99 / 1600 : ℝ) ≤ (17349516793 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (99 / 800 : ℝ)) (1422177665745473 / 400000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (99 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell98_product_upper
  have hD : (337865908999 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (49 / 400 : ℝ) - (99 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell98_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell98_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (49 / 400 : ℝ) - (99 / 3200 : ℝ)) ≤
      (1 / (337865908999 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (337865908999 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((99 / 3200 : ℝ) - Real.pi * Real.exp (49 / 400 : ℝ)) ≤
      (2 / (337865908999 / 10000000000 : ℝ) : ℝ) := by
    rw [show (99 / 3200 : ℝ) - Real.pi * Real.exp (49 / 400 : ℝ) =
      -(Real.pi * Real.exp (49 / 400 : ℝ) - (99 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1422177665745473 / 400000000000000 : ℝ) ^ 2 - 6 *
      (1422177665745473 / 400000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell98_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (49 / 800 : ℝ) (99 / 1600 : ℝ)) :
    (17163162309 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17349516793 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell98_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell98_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell99_leftExp :
    (11317329023 / 10000000000 : ℝ) ≤ Real.exp (99 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (99 / 800 : ℝ) (1003874674717 / 1000000000000 : ℝ)
    (11317329023 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell99_rightExp :
    Real.exp (1 / 8 : ℝ) ≤ (11331484531 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1 / 8 : ℝ) (1003913889339 / 1000000000000 : ℝ)
    (11331484531 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell99_denomUpper :
    Real.exp (35289537482197883 / 10000000000000000 : ℝ) ≤ (85220710059 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (35289537482197883 / 10000000000000000 : ℝ) (223318090787
    / 200000000000 : ℝ) (85220710059 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell99_denomLower :
    (339263850593 / 10000000000 : ℝ) ≤ Real.exp (4405241290003077 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4405241290003077 / 1250000000000000 : ℝ) (1116424348469
    / 1000000000000 : ℝ) (339263850593 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell99_product_lower :
    (4444303790003077 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (99 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell99_leftExp
    (by norm_num : (0 : ℝ) ≤ (11317329023 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell99_product_upper :
    Real.pi * Real.exp (1 / 8 : ℝ) ≤ (35598912482197883 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell99_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell99_endpointLower :
    (4287696383 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (99 / 1600 : ℝ) (1 / 16 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4444303790003077 / 1250000000000000 : ℝ) (Real.pi * Real.exp (99 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell99_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1 / 8 : ℝ) - (99 / 3200 : ℝ)) ≤
      (85220710059 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell99_denomUpper
    linarith [hpThetaJensenCell99_product_upper]
  have hi : (1 / (85220710059 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1 / 8 : ℝ) - (99 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (85220710059 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (85220710059 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((99 / 3200 : ℝ) - Real.pi * Real.exp (1 / 8 : ℝ)) := by
    rw [show (99 / 3200 : ℝ) - Real.pi * Real.exp (1 / 8 : ℝ) =
      -(Real.pi * Real.exp (1 / 8 : ℝ) - (99 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (99 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (99 / 800 : ℝ)) := by
    have h := hpThetaJensenCell99_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (85220710059 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell99_endpointUpper :
    hpThetaJensenKernelEndpointUpper (99 / 1600 : ℝ) (1 / 16 : ℝ) ≤ (17337067763 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1 / 8 : ℝ)) (35598912482197883 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1 / 16 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell99_product_upper
  have hD : (339263850593 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (99 / 800 : ℝ) - (1 / 32 : ℝ)) := by
    apply le_trans hpThetaJensenCell99_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell99_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (99 / 800 : ℝ) - (1 / 32 : ℝ)) ≤
      (1 / (339263850593 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (339263850593 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1 / 32 : ℝ) - Real.pi * Real.exp (99 / 800 : ℝ)) ≤
      (2 / (339263850593 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1 / 32 : ℝ) - Real.pi * Real.exp (99 / 800 : ℝ) =
      -(Real.pi * Real.exp (99 / 800 : ℝ) - (1 / 32 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (35598912482197883 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (35598912482197883 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell99_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (99 / 1600 : ℝ) (1 / 16 : ℝ)) :
    (4287696383 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17337067763 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell99_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell99_endpointUpper

def hpThetaJensenCellsBatch004Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1736510387 / 1000000000 : ℝ)
  | 1 => (17354933089 / 10000000000 : ℝ)
  | 2 => (4336159439 / 2500000000 : ℝ)
  | 3 => (4333554523 / 2500000000 : ℝ)
  | 4 => (8661837161 / 5000000000 : ℝ)
  | 5 => (8656503341 / 5000000000 : ℝ)
  | 6 => (1730221539 / 1000000000 : ℝ)
  | 7 => (17291300691 / 10000000000 : ℝ)
  | 8 => (17280262813 / 10000000000 : ℝ)
  | 9 => (17269101993 / 10000000000 : ℝ)
  | 10 => (4314454619 / 2500000000 : ℝ)
  | 11 => (1724641249 / 1000000000 : ℝ)
  | 12 => (1723488429 / 1000000000 : ℝ)
  | 13 => (3444646823 / 2000000000 : ℝ)
  | 14 => (17211462211 / 10000000000 : ℝ)
  | 15 => (17199568823 / 10000000000 : ℝ)
  | 16 => (3437510843 / 2000000000 : ℝ)
  | 17 => (137403349 / 80000000 : ℝ)
  | 18 => (17163162309 / 10000000000 : ℝ)
  | 19 => (4287696383 / 2500000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch004Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (8776279023 / 5000000000 : ℝ)
  | 1 => (17542336181 / 10000000000 : ℝ)
  | 2 => (17531988579 / 10000000000 : ℝ)
  | 3 => (17521515469 / 10000000000 : ℝ)
  | 4 => (17510917077 / 10000000000 : ℝ)
  | 5 => (17500193629 / 10000000000 : ℝ)
  | 6 => (4372336341 / 2500000000 : ℝ)
  | 7 => (8739186253 / 5000000000 : ℝ)
  | 8 => (8733637647 / 5000000000 : ℝ)
  | 9 => (3491210793 / 2000000000 : ℝ)
  | 10 => (8722354377 / 5000000000 : ℝ)
  | 11 => (17433239909 / 10000000000 : ℝ)
  | 12 => (8710823833 / 5000000000 : ℝ)
  | 13 => (8704966137 / 5000000000 : ℝ)
  | 14 => (17398093979 / 10000000000 : ℝ)
  | 15 => (17386133037 / 10000000000 : ℝ)
  | 16 => (8687024841 / 5000000000 : ℝ)
  | 17 => (17361844183 / 10000000000 : ℝ)
  | 18 => (17349516793 / 10000000000 : ℝ)
  | 19 => (17337067763 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch004_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((80 : ℝ) + (j.val : ℝ)) / 1600)
      (((80 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch004Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch004Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell80_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell81_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell82_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell83_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell84_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell85_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell86_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell87_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell88_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell89_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell90_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell91_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell92_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell93_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell94_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell95_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell96_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell97_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell98_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell99_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper] at h ⊢
    exact h

end HodgeProofHP
