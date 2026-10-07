import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell500_leftExp :
    (18682459573 / 10000000000 : ℝ) ≤ Real.exp (5 / 8 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5 / 8 : ℝ) (1019723232713 / 1000000000000 : ℝ)
    (18682459573 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell500_rightExp :
    Real.exp (501 / 800 : ℝ) ≤ (18705827251 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (501 / 800 : ℝ) (1019763066431 / 1000000000000 : ℝ)
    (18705827251 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell500_denomUpper :
    Real.exp (57203595950950843 / 10000000000000000 : ℝ) ≤ (95317057811 / 312500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (57203595950950843 / 10000000000000000 : ℝ)
    (1195735213171 / 1000000000000 : ℝ) (95317057811 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell500_denomLower :
    (756721121041 / 2500000000 : ℝ) ≤ Real.exp (7140880066857527 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7140880066857527 / 1250000000000000 : ℝ) (37357787027 /
    31250000000 : ℝ) (756721121041 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell500_product_lower :
    (7336583191857527 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (5 / 8 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell500_leftExp
    (by norm_num : (0 : ℝ) ≤ (18682459573 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell500_product_upper :
    Real.pi * Real.exp (501 / 800 : ℝ) ≤ (58766095950950843 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell500_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell500_endpointLower :
    (26904303 / 40000000 : ℝ) ≤ hpThetaTraceEndpointLower (5 / 16 : ℝ) (501 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7336583191857527 / 1250000000000000 : ℝ) (Real.pi * Real.exp (5 / 8 : ℝ))
    (by norm_num) hpThetaJensenCell500_product_lower
  have hD : Real.exp (Real.pi * Real.exp (501 / 800 : ℝ) - (5 / 32 : ℝ)) ≤
      (95317057811 / 312500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell500_denomUpper
    linarith [hpThetaJensenCell500_product_upper]
  have hi : (1 / (95317057811 / 312500000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (501 / 800 : ℝ) - (5 / 32 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (95317057811 / 312500000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (95317057811 / 312500000 : ℝ) : ℝ) ≤
      2 * Real.exp ((5 / 32 : ℝ) - Real.pi * Real.exp (501 / 800 : ℝ)) := by
    rw [show (5 / 32 : ℝ) - Real.pi * Real.exp (501 / 800 : ℝ) =
      -(Real.pi * Real.exp (501 / 800 : ℝ) - (5 / 32 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (5 / 8 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (5 / 8 : ℝ)) := by
    have h := hpThetaJensenCell500_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (95317057811 / 312500000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell500_endpointUpper :
    hpThetaJensenKernelEndpointUpper (5 / 16 : ℝ) (501 / 1600 : ℝ) ≤ (6815551617 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (501 / 800 : ℝ)) (58766095950950843 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (501 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell500_product_upper
  have hD : (756721121041 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (5 / 8 : ℝ) - (501 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell500_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell500_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (5 / 8 : ℝ) - (501 / 3200 : ℝ)) ≤
      (1 / (756721121041 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (756721121041 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((501 / 3200 : ℝ) - Real.pi * Real.exp (5 / 8 : ℝ)) ≤
      (2 / (756721121041 / 2500000000 : ℝ) : ℝ) := by
    rw [show (501 / 3200 : ℝ) - Real.pi * Real.exp (5 / 8 : ℝ) =
      -(Real.pi * Real.exp (5 / 8 : ℝ) - (501 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (58766095950950843 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (58766095950950843 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell500_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (5 / 16 : ℝ) (501 / 1600 : ℝ)) :
    (26904303 / 40000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6815551617 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell500_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell500_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell501_leftExp :
    (74823309 / 40000000 : ℝ) ≤ Real.exp (501 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (501 / 800 : ℝ) (101976306643 / 100000000000 : ℝ)
    (74823309 / 40000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell501_rightExp :
    Real.exp (251 / 400 : ℝ) ≤ (4682306039 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (251 / 400 : ℝ) (127475362713 / 125000000000 : ℝ)
    (4682306039 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell501_denomUpper :
    Real.exp (14318493625980127 / 2500000000000000 : ℝ) ≤ (767922012889 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (14318493625980127 / 2500000000000000 : ℝ) (597999111849
    / 500000000000 : ℝ) (767922012889 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell501_denomLower :
    (3048234401321 / 10000000000 : ℝ) ≤ Real.exp (28598663620991 / 5000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (28598663620991 / 5000000000000 : ℝ) (597855894643 /
    500000000000 : ℝ) (3048234401321 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell501_product_lower :
    (29383038620991 / 5000000000000 : ℝ) ≤ Real.pi * Real.exp (501 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell501_leftExp
    (by norm_num : (0 : ℝ) ≤ (74823309 / 40000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell501_product_upper :
    Real.pi * Real.exp (251 / 400 : ℝ) ≤ (14709899875980127 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell501_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell501_endpointLower :
    (6698494463 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (501 / 1600 : ℝ) (251 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (29383038620991 / 5000000000000 : ℝ) (Real.pi * Real.exp (501 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell501_product_lower
  have hD : Real.exp (Real.pi * Real.exp (251 / 400 : ℝ) - (501 / 3200 : ℝ)) ≤
      (767922012889 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell501_denomUpper
    linarith [hpThetaJensenCell501_product_upper]
  have hi : (1 / (767922012889 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (251 / 400 : ℝ) - (501 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (767922012889 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (767922012889 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((501 / 3200 : ℝ) - Real.pi * Real.exp (251 / 400 : ℝ)) := by
    rw [show (501 / 3200 : ℝ) - Real.pi * Real.exp (251 / 400 : ℝ) =
      -(Real.pi * Real.exp (251 / 400 : ℝ) - (501 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (501 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (501 / 800 : ℝ)) := by
    have h := hpThetaJensenCell501_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (767922012889 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell501_endpointUpper :
    hpThetaJensenKernelEndpointUpper (501 / 1600 : ℝ) (251 / 800 : ℝ) ≤ (84845761 / 125000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (251 / 400 : ℝ)) (14709899875980127 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (251 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell501_product_upper
  have hD : (3048234401321 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (501 / 800 : ℝ) - (251 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell501_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell501_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (501 / 800 : ℝ) - (251 / 1600 : ℝ)) ≤
      (1 / (3048234401321 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3048234401321 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((251 / 1600 : ℝ) - Real.pi * Real.exp (501 / 800 : ℝ)) ≤
      (2 / (3048234401321 / 10000000000 : ℝ) : ℝ) := by
    rw [show (251 / 1600 : ℝ) - Real.pi * Real.exp (501 / 800 : ℝ) =
      -(Real.pi * Real.exp (501 / 800 : ℝ) - (251 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (14709899875980127 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (14709899875980127 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell501_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (501 / 1600 : ℝ) (251 / 800 : ℝ)) :
    (6698494463 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (84845761 / 125000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell501_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell501_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell502_leftExp :
    (9364612077 / 5000000000 : ℝ) ≤ Real.exp (251 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (251 / 400 : ℝ) (1019802901703 / 1000000000000 : ℝ)
    (9364612077 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell502_rightExp :
    Real.exp (503 / 800 : ℝ) ≤ (4688162581 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (503 / 800 : ℝ) (1019842738533 / 1000000000000 : ℝ)
    (4688162581 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell502_denomUpper :
    Real.exp (14336111247331533 / 2500000000000000 : ℝ) ≤ (19333817733 / 62500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (14336111247331533 / 2500000000000000 : ℝ) (4785046543 /
    4000000000 : ℝ) (19333817733 / 62500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell502_denomLower :
    (767440773737 / 2500000000 : ℝ) ≤ Real.exp (3579231610525823 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3579231610525823 / 625000000000000 : ℝ) (1195974794563 /
    1000000000000 : ℝ) (767440773737 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell502_product_lower :
    (3677473798025823 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (251 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell502_leftExp
    (by norm_num : (0 : ℝ) ≤ (9364612077 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell502_product_upper :
    Real.pi * Real.exp (503 / 800 : ℝ) ≤ (14728298747331533 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell502_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell502_endpointLower :
    (6670960151 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (251 / 800 : ℝ) (503 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3677473798025823 / 625000000000000 : ℝ) (Real.pi * Real.exp (251 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell502_product_lower
  have hD : Real.exp (Real.pi * Real.exp (503 / 800 : ℝ) - (251 / 1600 : ℝ)) ≤
      (19333817733 / 62500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell502_denomUpper
    linarith [hpThetaJensenCell502_product_upper]
  have hi : (1 / (19333817733 / 62500000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (503 / 800 : ℝ) - (251 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (19333817733 / 62500000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (19333817733 / 62500000 : ℝ) : ℝ) ≤
      2 * Real.exp ((251 / 1600 : ℝ) - Real.pi * Real.exp (503 / 800 : ℝ)) := by
    rw [show (251 / 1600 : ℝ) - Real.pi * Real.exp (503 / 800 : ℝ) =
      -(Real.pi * Real.exp (503 / 800 : ℝ) - (251 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (251 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (251 / 400 : ℝ)) := by
    have h := hpThetaJensenCell502_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (19333817733 / 62500000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell502_endpointUpper :
    hpThetaJensenKernelEndpointUpper (251 / 800 : ℝ) (503 / 1600 : ℝ) ≤ (3379908679 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (503 / 800 : ℝ)) (14728298747331533 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (503 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell502_product_upper
  have hD : (767440773737 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (251 / 400 : ℝ) - (503 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell502_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell502_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (251 / 400 : ℝ) - (503 / 3200 : ℝ)) ≤
      (1 / (767440773737 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (767440773737 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((503 / 3200 : ℝ) - Real.pi * Real.exp (251 / 400 : ℝ)) ≤
      (2 / (767440773737 / 2500000000 : ℝ) : ℝ) := by
    rw [show (503 / 3200 : ℝ) - Real.pi * Real.exp (251 / 400 : ℝ) =
      -(Real.pi * Real.exp (251 / 400 : ℝ) - (503 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (14728298747331533 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (14728298747331533 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell502_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (251 / 800 : ℝ) (503 / 1600 : ℝ)) :
    (6670960151 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3379908679 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell502_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell502_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell503_leftExp :
    (9376325161 / 5000000000 : ℝ) ≤ Real.exp (503 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (503 / 800 : ℝ) (254960684633 / 250000000000 : ℝ)
    (9376325161 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell503_rightExp :
    Real.exp (63 / 100 : ℝ) ≤ (9388052897 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (63 / 100 : ℝ) (509941288459 / 500000000000 : ℝ)
    (9388052897 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell503_denomUpper :
    Real.exp (28707503764844921 / 5000000000000000 : ℝ) ≤ (62306318459 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (28707503764844921 / 5000000000000000 : ℝ) (598262725011
    / 500000000000 : ℝ) (62306318459 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell503_denomLower :
    (61829445203 / 200000000 : ℝ) ≤ Real.exp (3583636014399539 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3583636014399539 / 625000000000000 : ℝ) (598119100683 /
    500000000000 : ℝ) (61829445203 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell503_product_lower :
    (3682073514399539 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (503 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell503_leftExp
    (by norm_num : (0 : ℝ) ≤ (9376325161 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell503_product_upper :
    Real.pi * Real.exp (63 / 100 : ℝ) ≤ (29493441264844921 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell503_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell503_endpointLower :
    (830434137 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (503 / 1600 : ℝ) (63 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3682073514399539 / 625000000000000 : ℝ) (Real.pi * Real.exp (503 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell503_product_lower
  have hD : Real.exp (Real.pi * Real.exp (63 / 100 : ℝ) - (503 / 3200 : ℝ)) ≤
      (62306318459 / 200000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell503_denomUpper
    linarith [hpThetaJensenCell503_product_upper]
  have hi : (1 / (62306318459 / 200000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (63 / 100 : ℝ) - (503 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (62306318459 / 200000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (62306318459 / 200000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((503 / 3200 : ℝ) - Real.pi * Real.exp (63 / 100 : ℝ)) := by
    rw [show (503 / 3200 : ℝ) - Real.pi * Real.exp (63 / 100 : ℝ) =
      -(Real.pi * Real.exp (63 / 100 : ℝ) - (503 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (503 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (503 / 800 : ℝ)) := by
    have h := hpThetaJensenCell503_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (62306318459 / 200000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell503_endpointUpper :
    hpThetaJensenKernelEndpointUpper (503 / 1600 : ℝ) (63 / 200 : ℝ) ≤ (3366010671 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (63 / 100 : ℝ)) (29493441264844921 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (63 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell503_product_upper
  have hD : (61829445203 / 200000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (503 / 800 : ℝ) - (63 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell503_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell503_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (503 / 800 : ℝ) - (63 / 400 : ℝ)) ≤
      (1 / (61829445203 / 200000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (61829445203 / 200000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((63 / 400 : ℝ) - Real.pi * Real.exp (503 / 800 : ℝ)) ≤
      (2 / (61829445203 / 200000000 : ℝ) : ℝ) := by
    rw [show (63 / 400 : ℝ) - Real.pi * Real.exp (503 / 800 : ℝ) =
      -(Real.pi * Real.exp (503 / 800 : ℝ) - (63 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (29493441264844921 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (29493441264844921 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell503_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (503 / 1600 : ℝ) (63 / 200 : ℝ)) :
    (830434137 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3366010671 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell503_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell503_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell504_leftExp :
    (293376653 / 156250000 : ℝ) ≤ Real.exp (63 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (63 / 100 : ℝ) (1019882576917 / 1000000000000 : ℝ)
    (293376653 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell504_rightExp :
    Real.exp (101 / 160 : ℝ) ≤ (18799590601 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (101 / 160 : ℝ) (1019922416859 / 1000000000000 : ℝ)
    (18799590601 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell504_denomUpper :
    Real.exp (57485662234967393 / 10000000000000000 : ℝ) ≤ (784351259741 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (57485662234967393 / 10000000000000000 : ℝ)
    (1196789667169 / 1000000000000 : ℝ) (784351259741 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell504_denomLower :
    (3113363611111 / 10000000000 : ℝ) ≤ Real.exp (56063221432911 / 9765625000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (56063221432911 / 9765625000000 : ℝ) (1196502010383 /
    1000000000000 : ℝ) (3113363611111 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell504_product_lower :
    (115208718256447 / 19531250000000 : ℝ) ≤ Real.pi * Real.exp (63 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell504_leftExp
    (by norm_num : (0 : ℝ) ≤ (293376653 / 156250000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell504_product_upper :
    Real.pi * Real.exp (101 / 160 : ℝ) ≤ (59060662234967393 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell504_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell504_endpointLower :
    (1323206717 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (63 / 200 : ℝ) (101 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (115208718256447 / 19531250000000 : ℝ) (Real.pi * Real.exp (63 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell504_product_lower
  have hD : Real.exp (Real.pi * Real.exp (101 / 160 : ℝ) - (63 / 400 : ℝ)) ≤
      (784351259741 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell504_denomUpper
    linarith [hpThetaJensenCell504_product_upper]
  have hi : (1 / (784351259741 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (101 / 160 : ℝ) - (63 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (784351259741 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (784351259741 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((63 / 400 : ℝ) - Real.pi * Real.exp (101 / 160 : ℝ)) := by
    rw [show (63 / 400 : ℝ) - Real.pi * Real.exp (101 / 160 : ℝ) =
      -(Real.pi * Real.exp (101 / 160 : ℝ) - (63 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (63 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (63 / 100 : ℝ)) := by
    have h := hpThetaJensenCell504_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (784351259741 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell504_endpointUpper :
    hpThetaJensenKernelEndpointUpper (63 / 200 : ℝ) (101 / 320 : ℝ) ≤ (6704273113 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (101 / 160 : ℝ)) (59060662234967393 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (101 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell504_product_upper
  have hD : (3113363611111 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (63 / 100 : ℝ) - (101 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell504_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell504_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (63 / 100 : ℝ) - (101 / 640 : ℝ)) ≤
      (1 / (3113363611111 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3113363611111 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((101 / 640 : ℝ) - Real.pi * Real.exp (63 / 100 : ℝ)) ≤
      (2 / (3113363611111 / 10000000000 : ℝ) : ℝ) := by
    rw [show (101 / 640 : ℝ) - Real.pi * Real.exp (63 / 100 : ℝ) =
      -(Real.pi * Real.exp (63 / 100 : ℝ) - (101 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (59060662234967393 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (59060662234967393 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell504_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (63 / 200 : ℝ) (101 / 320 : ℝ)) :
    (1323206717 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6704273113 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell504_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell504_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell505_leftExp :
    (18799590599 / 10000000000 : ℝ) ≤ Real.exp (101 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (101 / 160 : ℝ) (509961208429 / 500000000000 : ℝ)
    (18799590599 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell505_rightExp :
    Real.exp (253 / 400 : ℝ) ≤ (9411552391 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (253 / 400 : ℝ) (1019962258357 / 1000000000000 : ℝ)
    (9411552391 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell505_denomUpper :
    Real.exp (28778204610698863 / 5000000000000000 : ℝ) ≤ (789919983819 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (28778204610698863 / 5000000000000000 : ℝ) (149631785983
    / 125000000000 : ℝ) (789919983819 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell505_denomLower :
    (97982464903 / 312500000 : ℝ) ≤ Real.exp (7184924178636701 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7184924178636701 / 1250000000000000 : ℝ) (598383111133 /
    500000000000 : ℝ) (97982464903 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell505_product_lower :
    (7382580428636701 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (101 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell505_leftExp
    (by norm_num : (0 : ℝ) ≤ (18799590599 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell505_product_upper :
    Real.pi * Real.exp (253 / 400 : ℝ) ≤ (29567267110698863 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell505_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell505_endpointLower :
    (3294320949 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (101 / 320 : ℝ) (253 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7382580428636701 / 1250000000000000 : ℝ) (Real.pi * Real.exp (101 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell505_product_lower
  have hD : Real.exp (Real.pi * Real.exp (253 / 400 : ℝ) - (101 / 640 : ℝ)) ≤
      (789919983819 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell505_denomUpper
    linarith [hpThetaJensenCell505_product_upper]
  have hi : (1 / (789919983819 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (253 / 400 : ℝ) - (101 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (789919983819 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (789919983819 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((101 / 640 : ℝ) - Real.pi * Real.exp (253 / 400 : ℝ)) := by
    rw [show (101 / 640 : ℝ) - Real.pi * Real.exp (253 / 400 : ℝ) =
      -(Real.pi * Real.exp (253 / 400 : ℝ) - (101 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (101 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (101 / 160 : ℝ)) := by
    have h := hpThetaJensenCell505_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (789919983819 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell505_endpointUpper :
    hpThetaJensenKernelEndpointUpper (101 / 320 : ℝ) (253 / 800 : ℝ) ≤ (6676572963 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (253 / 400 : ℝ)) (29567267110698863 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (253 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell505_product_upper
  have hD : (97982464903 / 312500000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (101 / 160 : ℝ) - (253 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell505_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell505_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (101 / 160 : ℝ) - (253 / 1600 : ℝ)) ≤
      (1 / (97982464903 / 312500000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (97982464903 / 312500000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((253 / 1600 : ℝ) - Real.pi * Real.exp (101 / 160 : ℝ)) ≤
      (2 / (97982464903 / 312500000 : ℝ) : ℝ) := by
    rw [show (253 / 1600 : ℝ) - Real.pi * Real.exp (101 / 160 : ℝ) =
      -(Real.pi * Real.exp (101 / 160 : ℝ) - (253 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (29567267110698863 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (29567267110698863 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell505_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (101 / 320 : ℝ) (253 / 800 : ℝ)) :
    (3294320949 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6676572963 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell505_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell505_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell506_leftExp :
    (18823104781 / 10000000000 : ℝ) ≤ Real.exp (253 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (253 / 400 : ℝ) (254990564589 / 250000000000 : ℝ)
    (18823104781 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell506_rightExp :
    Real.exp (507 / 800 : ℝ) ≤ (150773187 / 80000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (507 / 800 : ℝ) (1020002101411 / 1000000000000 : ℝ)
    (150773187 / 80000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell506_denomUpper :
    Real.exp (461017988866891 / 80000000000000 : ℝ) ≤ (3182142381571 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (461017988866891 / 80000000000000 : ℝ) (1197319312797 /
    1000000000000 : ℝ) (3182142381571 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell506_denomLower :
    (3157699807457 / 10000000000 : ℝ) ≤ Real.exp (7193767549393919 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7193767549393919 / 1250000000000000 : ℝ) (1197030837701
    / 1000000000000 : ℝ) (3157699807457 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell506_product_lower :
    (7391814424393919 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (253 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell506_leftExp
    (by norm_num : (0 : ℝ) ≤ (18823104781 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell506_product_upper :
    Real.pi * Real.exp (507 / 800 : ℝ) ≤ (473667988866891 / 80000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell506_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell506_endpointLower :
    (6561298313 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (253 / 800 : ℝ) (507 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7391814424393919 / 1250000000000000 : ℝ) (Real.pi * Real.exp (253 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell506_product_lower
  have hD : Real.exp (Real.pi * Real.exp (507 / 800 : ℝ) - (253 / 1600 : ℝ)) ≤
      (3182142381571 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell506_denomUpper
    linarith [hpThetaJensenCell506_product_upper]
  have hi : (1 / (3182142381571 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (507 / 800 : ℝ) - (253 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3182142381571 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3182142381571 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((253 / 1600 : ℝ) - Real.pi * Real.exp (507 / 800 : ℝ)) := by
    rw [show (253 / 1600 : ℝ) - Real.pi * Real.exp (507 / 800 : ℝ) =
      -(Real.pi * Real.exp (507 / 800 : ℝ) - (253 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (253 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (253 / 400 : ℝ)) := by
    have h := hpThetaJensenCell506_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3182142381571 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell506_endpointUpper :
    hpThetaJensenKernelEndpointUpper (253 / 800 : ℝ) (507 / 1600 : ℝ) ≤ (1662230293 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (507 / 800 : ℝ)) (473667988866891 / 80000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (507 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell506_product_upper
  have hD : (3157699807457 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (253 / 400 : ℝ) - (507 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell506_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell506_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (253 / 400 : ℝ) - (507 / 3200 : ℝ)) ≤
      (1 / (3157699807457 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3157699807457 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((507 / 3200 : ℝ) - Real.pi * Real.exp (253 / 400 : ℝ)) ≤
      (2 / (3157699807457 / 10000000000 : ℝ) : ℝ) := by
    rw [show (507 / 3200 : ℝ) - Real.pi * Real.exp (253 / 400 : ℝ) =
      -(Real.pi * Real.exp (253 / 400 : ℝ) - (507 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (473667988866891 / 80000000000000 : ℝ) ^ 2 - 6 *
      (473667988866891 / 80000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell506_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (253 / 800 : ℝ) (507 / 1600 : ℝ)) :
    (6561298313 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1662230293 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell506_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell506_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell507_leftExp :
    (9423324187 / 5000000000 : ℝ) ≤ Real.exp (507 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (507 / 800 : ℝ) (102000210141 / 100000000000 : ℝ)
    (9423324187 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell507_rightExp :
    Real.exp (127 / 200 : ℝ) ≤ (3774044283 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (127 / 200 : ℝ) (1020041946021 / 1000000000000 : ℝ)
    (3774044283 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell507_denomUpper :
    Real.exp (11539636101162819 / 2000000000000000 : ℝ) ≤ (160239708153 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11539636101162819 / 2000000000000000 : ℝ) (1197584742623
    / 1000000000000 : ℝ) (160239708153 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell507_denomLower :
    (795037042359 / 2500000000 : ℝ) ≤ Real.exp (3601311234910713 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3601311234910713 / 625000000000000 : ℝ) (239459171471 /
    200000000000 : ℝ) (795037042359 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell507_product_lower :
    (3700529984910713 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (507 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell507_leftExp
    (by norm_num : (0 : ℝ) ≤ (9423324187 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell507_product_upper :
    Real.pi * Real.exp (127 / 200 : ℝ) ≤ (11856511101162819 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell507_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell507_endpointLower :
    (653400311 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (507 / 1600 : ℝ) (127 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3700529984910713 / 625000000000000 : ℝ) (Real.pi * Real.exp (507 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell507_product_lower
  have hD : Real.exp (Real.pi * Real.exp (127 / 200 : ℝ) - (507 / 3200 : ℝ)) ≤
      (160239708153 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell507_denomUpper
    linarith [hpThetaJensenCell507_product_upper]
  have hi : (1 / (160239708153 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (127 / 200 : ℝ) - (507 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (160239708153 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (160239708153 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((507 / 3200 : ℝ) - Real.pi * Real.exp (127 / 200 : ℝ)) := by
    rw [show (507 / 3200 : ℝ) - Real.pi * Real.exp (127 / 200 : ℝ) =
      -(Real.pi * Real.exp (127 / 200 : ℝ) - (507 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (507 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (507 / 800 : ℝ)) := by
    have h := hpThetaJensenCell507_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (160239708153 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell507_endpointUpper :
    hpThetaJensenKernelEndpointUpper (507 / 1600 : ℝ) (127 / 400 : ℝ) ≤ (3310659011 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (127 / 200 : ℝ)) (11856511101162819 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (127 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell507_product_upper
  have hD : (795037042359 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (507 / 800 : ℝ) - (127 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell507_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell507_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (507 / 800 : ℝ) - (127 / 800 : ℝ)) ≤
      (1 / (795037042359 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (795037042359 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((127 / 800 : ℝ) - Real.pi * Real.exp (507 / 800 : ℝ)) ≤
      (2 / (795037042359 / 2500000000 : ℝ) : ℝ) := by
    rw [show (127 / 800 : ℝ) - Real.pi * Real.exp (507 / 800 : ℝ) =
      -(Real.pi * Real.exp (507 / 800 : ℝ) - (127 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (11856511101162819 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (11856511101162819 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell507_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (507 / 1600 : ℝ) (127 / 400 : ℝ)) :
    (653400311 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3310659011 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell507_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell507_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell508_leftExp :
    (9435110707 / 5000000000 : ℝ) ≤ Real.exp (127 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (127 / 200 : ℝ) (51002097301 / 50000000000 : ℝ)
    (9435110707 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell508_rightExp :
    Real.exp (509 / 800 : ℝ) ≤ (18893823941 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (509 / 800 : ℝ) (255020448047 / 250000000000 : ℝ)
    (18893823941 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell508_denomUpper :
    Real.exp (57769205036278013 / 10000000000000000 : ℝ) ≤ (1613818543747 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (57769205036278013 / 10000000000000000 : ℝ) (598925289021
    / 500000000000 : ℝ) (1613818543747 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell508_denomLower :
    (800696436919 / 2500000000 : ℝ) ≤ Real.exp (3605744477028193 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3605744477028193 / 625000000000000 : ℝ) (299390320473 /
    250000000000 : ℝ) (800696436919 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell508_product_lower :
    (3705158539528193 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (127 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell508_leftExp
    (by norm_num : (0 : ℝ) ≤ (9435110707 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell508_product_upper :
    Real.pi * Real.exp (509 / 800 : ℝ) ≤ (59356705036278013 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell508_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell508_endpointLower :
    (3253378281 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (127 / 400 : ℝ) (509 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3705158539528193 / 625000000000000 : ℝ) (Real.pi * Real.exp (127 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell508_product_lower
  have hD : Real.exp (Real.pi * Real.exp (509 / 800 : ℝ) - (127 / 800 : ℝ)) ≤
      (1613818543747 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell508_denomUpper
    linarith [hpThetaJensenCell508_product_upper]
  have hi : (1 / (1613818543747 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (509 / 800 : ℝ) - (127 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1613818543747 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1613818543747 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((127 / 800 : ℝ) - Real.pi * Real.exp (509 / 800 : ℝ)) := by
    rw [show (127 / 800 : ℝ) - Real.pi * Real.exp (509 / 800 : ℝ) =
      -(Real.pi * Real.exp (509 / 800 : ℝ) - (127 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (127 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (127 / 200 : ℝ)) := by
    have h := hpThetaJensenCell508_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1613818543747 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell508_endpointUpper :
    hpThetaJensenKernelEndpointUpper (127 / 400 : ℝ) (509 / 1600 : ℝ) ≤ (6593763797 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (509 / 800 : ℝ)) (59356705036278013 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (509 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell508_product_upper
  have hD : (800696436919 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (127 / 200 : ℝ) - (509 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell508_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell508_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (127 / 200 : ℝ) - (509 / 3200 : ℝ)) ≤
      (1 / (800696436919 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (800696436919 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((509 / 3200 : ℝ) - Real.pi * Real.exp (127 / 200 : ℝ)) ≤
      (2 / (800696436919 / 2500000000 : ℝ) : ℝ) := by
    rw [show (509 / 3200 : ℝ) - Real.pi * Real.exp (127 / 200 : ℝ) =
      -(Real.pi * Real.exp (127 / 200 : ℝ) - (509 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (59356705036278013 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (59356705036278013 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell508_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (127 / 400 : ℝ) (509 / 1600 : ℝ)) :
    (3253378281 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6593763797 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell508_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell508_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell509_leftExp :
    (18893823939 / 10000000000 : ℝ) ≤ Real.exp (509 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (509 / 800 : ℝ) (1020081792187 / 1000000000000 : ℝ)
    (18893823939 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell509_rightExp :
    Real.exp (51 / 80 : ℝ) ≤ (4729363997 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (51 / 80 : ℝ) (1020121639911 / 1000000000000 : ℝ)
    (4729363997 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell509_denomUpper :
    Real.exp (14460080577427221 / 2500000000000000 : ℝ) ≤ (812668244443 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (14460080577427221 / 2500000000000000 : ℝ) (119811681971
    / 100000000000 : ℝ) (812668244443 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell509_denomLower :
    (201600896751 / 625000000 : ℝ) ≤ Real.exp (7220367017021361 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7220367017021361 / 1250000000000000 : ℝ) (1197827112003
    / 1000000000000 : ℝ) (201600896751 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell509_product_lower :
    (7419585767021361 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (509 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell509_leftExp
    (by norm_num : (0 : ℝ) ≤ (18893823939 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell509_product_upper :
    Real.pi * Real.exp (51 / 80 : ℝ) ≤ (14857736827427221 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell509_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell509_endpointLower :
    (3239779473 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (509 / 1600 : ℝ) (51 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7419585767021361 / 1250000000000000 : ℝ) (Real.pi * Real.exp (509 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell509_product_lower
  have hD : Real.exp (Real.pi * Real.exp (51 / 80 : ℝ) - (509 / 3200 : ℝ)) ≤
      (812668244443 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell509_denomUpper
    linarith [hpThetaJensenCell509_product_upper]
  have hi : (1 / (812668244443 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (51 / 80 : ℝ) - (509 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (812668244443 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (812668244443 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((509 / 3200 : ℝ) - Real.pi * Real.exp (51 / 80 : ℝ)) := by
    rw [show (509 / 3200 : ℝ) - Real.pi * Real.exp (51 / 80 : ℝ) =
      -(Real.pi * Real.exp (51 / 80 : ℝ) - (509 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (509 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (509 / 800 : ℝ)) := by
    have h := hpThetaJensenCell509_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (812668244443 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell509_endpointUpper :
    hpThetaJensenKernelEndpointUpper (509 / 1600 : ℝ) (51 / 160 : ℝ) ≤ (656625877 / 1000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (51 / 80 : ℝ)) (14857736827427221 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (51 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell509_product_upper
  have hD : (201600896751 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (509 / 800 : ℝ) - (51 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell509_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell509_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (509 / 800 : ℝ) - (51 / 320 : ℝ)) ≤
      (1 / (201600896751 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (201600896751 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((51 / 320 : ℝ) - Real.pi * Real.exp (509 / 800 : ℝ)) ≤
      (2 / (201600896751 / 625000000 : ℝ) : ℝ) := by
    rw [show (51 / 320 : ℝ) - Real.pi * Real.exp (509 / 800 : ℝ) =
      -(Real.pi * Real.exp (509 / 800 : ℝ) - (51 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (14857736827427221 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (14857736827427221 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell509_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (509 / 1600 : ℝ) (51 / 160 : ℝ)) :
    (3239779473 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (656625877 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell509_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell509_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell510_leftExp :
    (9458727993 / 5000000000 : ℝ) ≤ Real.exp (51 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (51 / 80 : ℝ) (102012163991 / 100000000000 : ℝ)
    (9458727993 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell510_rightExp :
    Real.exp (511 / 800 : ℝ) ≤ (18941117593 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (511 / 800 : ℝ) (1020161489191 / 1000000000000 : ℝ)
    (18941117593 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell510_denomUpper :
    Real.exp (57911532442345649 / 10000000000000000 : ℝ) ≤ (1636951839033 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (57911532442345649 / 10000000000000000 : ℝ) (299595867077
    / 250000000000 : ℝ) (1636951839033 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell510_denomLower :
    (3248635794189 / 10000000000 : ℝ) ≤ Real.exp (3614628336623107 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3614628336623107 / 625000000000000 : ℝ) (1198093348367 /
    1000000000000 : ℝ) (3248635794189 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell510_product_lower :
    (3714433024123107 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (51 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell510_leftExp
    (by norm_num : (0 : ℝ) ≤ (9458727993 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell510_product_upper :
    Real.pi * Real.exp (511 / 800 : ℝ) ≤ (59505282442345649 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell510_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell510_endpointLower :
    (1290482107 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (51 / 160 : ℝ) (511 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3714433024123107 / 625000000000000 : ℝ) (Real.pi * Real.exp (51 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell510_product_lower
  have hD : Real.exp (Real.pi * Real.exp (511 / 800 : ℝ) - (51 / 320 : ℝ)) ≤
      (1636951839033 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell510_denomUpper
    linarith [hpThetaJensenCell510_product_upper]
  have hi : (1 / (1636951839033 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (511 / 800 : ℝ) - (51 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1636951839033 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1636951839033 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((51 / 320 : ℝ) - Real.pi * Real.exp (511 / 800 : ℝ)) := by
    rw [show (51 / 320 : ℝ) - Real.pi * Real.exp (511 / 800 : ℝ) =
      -(Real.pi * Real.exp (511 / 800 : ℝ) - (51 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (51 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (51 / 80 : ℝ)) := by
    have h := hpThetaJensenCell510_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1636951839033 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell510_endpointUpper :
    hpThetaJensenKernelEndpointUpper (51 / 160 : ℝ) (511 / 1600 : ℝ) ≤ (3269401609 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (511 / 800 : ℝ)) (59505282442345649 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (511 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell510_product_upper
  have hD : (3248635794189 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (51 / 80 : ℝ) - (511 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell510_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell510_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (51 / 80 : ℝ) - (511 / 3200 : ℝ)) ≤
      (1 / (3248635794189 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3248635794189 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((511 / 3200 : ℝ) - Real.pi * Real.exp (51 / 80 : ℝ)) ≤
      (2 / (3248635794189 / 10000000000 : ℝ) : ℝ) := by
    rw [show (511 / 3200 : ℝ) - Real.pi * Real.exp (51 / 80 : ℝ) =
      -(Real.pi * Real.exp (51 / 80 : ℝ) - (511 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (59505282442345649 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (59505282442345649 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell510_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (51 / 160 : ℝ) (511 / 1600 : ℝ)) :
    (1290482107 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3269401609 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell510_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell510_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell511_leftExp :
    (18941117591 / 10000000000 : ℝ) ≤ Real.exp (511 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (511 / 800 : ℝ) (102016148919 / 100000000000 : ℝ)
    (18941117591 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell511_rightExp :
    Real.exp (16 / 25 : ℝ) ≤ (9482404397 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (16 / 25 : ℝ) (1020201340027 / 1000000000000 : ℝ)
    (9482404397 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell511_denomUpper :
    Real.exp (28991417776784421 / 5000000000000000 : ℝ) ≤ (3297331052869 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (28991417776784421 / 5000000000000000 : ℝ) (74915657783 /
    62500000000 : ℝ) (3297331052869 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell511_denomLower :
    (1635925964091 / 5000000000 : ℝ) ≤ Real.exp (7238157936868109 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7238157936868109 / 1250000000000000 : ℝ) (1198359991653
    / 1000000000000 : ℝ) (1635925964091 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell511_product_lower :
    (7438157936868109 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (511 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell511_leftExp
    (by norm_num : (0 : ℝ) ≤ (18941117591 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell511_product_upper :
    Real.pi * Real.exp (16 / 25 : ℝ) ≤ (29789855276784421 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell511_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell511_endpointLower :
    (1285062319 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (511 / 1600 : ℝ) (8 / 25 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7438157936868109 / 1250000000000000 : ℝ) (Real.pi * Real.exp (511 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell511_product_lower
  have hD : Real.exp (Real.pi * Real.exp (16 / 25 : ℝ) - (511 / 3200 : ℝ)) ≤
      (3297331052869 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell511_denomUpper
    linarith [hpThetaJensenCell511_product_upper]
  have hi : (1 / (3297331052869 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (16 / 25 : ℝ) - (511 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3297331052869 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3297331052869 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((511 / 3200 : ℝ) - Real.pi * Real.exp (16 / 25 : ℝ)) := by
    rw [show (511 / 3200 : ℝ) - Real.pi * Real.exp (16 / 25 : ℝ) =
      -(Real.pi * Real.exp (16 / 25 : ℝ) - (511 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (511 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (511 / 800 : ℝ)) := by
    have h := hpThetaJensenCell511_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3297331052869 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell511_endpointUpper :
    hpThetaJensenKernelEndpointUpper (511 / 1600 : ℝ) (8 / 25 : ℝ) ≤ (813924677 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (16 / 25 : ℝ)) (29789855276784421 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (8 / 25 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell511_product_upper
  have hD : (1635925964091 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (511 / 800 : ℝ) - (4 / 25 : ℝ)) := by
    apply le_trans hpThetaJensenCell511_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell511_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (511 / 800 : ℝ) - (4 / 25 : ℝ)) ≤
      (1 / (1635925964091 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1635925964091 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((4 / 25 : ℝ) - Real.pi * Real.exp (511 / 800 : ℝ)) ≤
      (2 / (1635925964091 / 5000000000 : ℝ) : ℝ) := by
    rw [show (4 / 25 : ℝ) - Real.pi * Real.exp (511 / 800 : ℝ) =
      -(Real.pi * Real.exp (511 / 800 : ℝ) - (4 / 25 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (29789855276784421 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (29789855276784421 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell511_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (511 / 1600 : ℝ) (8 / 25 : ℝ)) :
    (1285062319 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (813924677 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell511_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell511_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell512_leftExp :
    (2370601099 / 1250000000 : ℝ) ≤ Real.exp (16 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (16 / 25 : ℝ) (510100670013 / 500000000000 : ℝ)
    (2370601099 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell512_rightExp :
    Real.exp (513 / 800 : ℝ) ≤ (18988529627 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (513 / 800 : ℝ) (51012059621 / 50000000000 : ℝ)
    (18988529627 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell512_denomUpper :
    Real.exp (58054231756475811 / 10000000000000000 : ℝ) ≤ (3320956984333 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (58054231756475811 / 10000000000000000 : ℝ) (14986474863
    / 12500000000 : ℝ) (3320956984333 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell512_denomLower :
    (3295264613233 / 10000000000 : ℝ) ≤ Real.exp (905883852851201 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (905883852851201 / 156250000000000 : ℝ) (149828380319 /
    125000000000 : ℝ) (3295264613233 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell512_product_lower :
    (930932680976201 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (16 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell512_leftExp
    (by norm_num : (0 : ℝ) ≤ (2370601099 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell512_product_upper :
    Real.pi * Real.exp (513 / 800 : ℝ) ≤ (59654231756475811 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell512_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell512_endpointLower :
    (6398262399 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (8 / 25 : ℝ) (513 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (930932680976201 / 156250000000000 : ℝ) (Real.pi * Real.exp (16 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell512_product_lower
  have hD : Real.exp (Real.pi * Real.exp (513 / 800 : ℝ) - (4 / 25 : ℝ)) ≤
      (3320956984333 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell512_denomUpper
    linarith [hpThetaJensenCell512_product_upper]
  have hi : (1 / (3320956984333 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (513 / 800 : ℝ) - (4 / 25 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3320956984333 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3320956984333 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((4 / 25 : ℝ) - Real.pi * Real.exp (513 / 800 : ℝ)) := by
    rw [show (4 / 25 : ℝ) - Real.pi * Real.exp (513 / 800 : ℝ) =
      -(Real.pi * Real.exp (513 / 800 : ℝ) - (4 / 25 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (16 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (16 / 25 : ℝ)) := by
    have h := hpThetaJensenCell512_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3320956984333 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell512_endpointUpper :
    hpThetaJensenKernelEndpointUpper (8 / 25 : ℝ) (513 / 1600 : ℝ) ≤ (1621010409 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (513 / 800 : ℝ)) (59654231756475811 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (513 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell512_product_upper
  have hD : (3295264613233 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (16 / 25 : ℝ) - (513 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell512_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell512_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (16 / 25 : ℝ) - (513 / 3200 : ℝ)) ≤
      (1 / (3295264613233 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3295264613233 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((513 / 3200 : ℝ) - Real.pi * Real.exp (16 / 25 : ℝ)) ≤
      (2 / (3295264613233 / 10000000000 : ℝ) : ℝ) := by
    rw [show (513 / 3200 : ℝ) - Real.pi * Real.exp (16 / 25 : ℝ) =
      -(Real.pi * Real.exp (16 / 25 : ℝ) - (513 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (59654231756475811 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (59654231756475811 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell512_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (8 / 25 : ℝ) (513 / 1600 : ℝ)) :
    (6398262399 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1621010409 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell512_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell512_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell513_leftExp :
    (151908237 / 80000000 : ℝ) ≤ Real.exp (513 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (513 / 800 : ℝ) (1020241192419 / 1000000000000 : ℝ)
    (151908237 / 80000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell513_rightExp :
    Real.exp (257 / 400 : ℝ) ≤ (1901228013 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (257 / 400 : ℝ) (102028104637 / 100000000000 : ℝ)
    (1901228013 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell513_denomUpper :
    Real.exp (5812572117044709 / 1000000000000000 : ℝ) ≤ (1672391688217 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (5812572117044709 / 1000000000000000 : ℝ) (1199185862537
    / 1000000000000 : ℝ) (1672391688217 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell513_denomLower :
    (3318875730401 / 10000000000 : ℝ) ≤ Real.exp (58047962761663 / 10000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (58047962761663 / 10000000000000 : ℝ) (239778900347 /
    200000000000 : ℝ) (3318875730401 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell513_product_lower :
    (59654212761663 / 10000000000000 : ℝ) ≤ Real.pi * Real.exp (513 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell513_leftExp
    (by norm_num : (0 : ℝ) ≤ (151908237 / 80000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell513_product_upper :
    Real.pi * Real.exp (257 / 400 : ℝ) ≤ (5972884617044709 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell513_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell513_endpointLower :
    (6371263209 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (513 / 1600 : ℝ) (257 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (59654212761663 / 10000000000000 : ℝ) (Real.pi * Real.exp (513 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell513_product_lower
  have hD : Real.exp (Real.pi * Real.exp (257 / 400 : ℝ) - (513 / 3200 : ℝ)) ≤
      (1672391688217 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell513_denomUpper
    linarith [hpThetaJensenCell513_product_upper]
  have hi : (1 / (1672391688217 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (257 / 400 : ℝ) - (513 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1672391688217 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1672391688217 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((513 / 3200 : ℝ) - Real.pi * Real.exp (257 / 400 : ℝ)) := by
    rw [show (513 / 3200 : ℝ) - Real.pi * Real.exp (257 / 400 : ℝ) =
      -(Real.pi * Real.exp (257 / 400 : ℝ) - (513 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (513 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (513 / 800 : ℝ)) := by
    have h := hpThetaJensenCell513_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1672391688217 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell513_endpointUpper :
    hpThetaJensenKernelEndpointUpper (513 / 1600 : ℝ) (257 / 800 : ℝ) ≤ (1614184037 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (257 / 400 : ℝ)) (5972884617044709 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (257 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell513_product_upper
  have hD : (3318875730401 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (513 / 800 : ℝ) - (257 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell513_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell513_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (513 / 800 : ℝ) - (257 / 1600 : ℝ)) ≤
      (1 / (3318875730401 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3318875730401 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((257 / 1600 : ℝ) - Real.pi * Real.exp (513 / 800 : ℝ)) ≤
      (2 / (3318875730401 / 10000000000 : ℝ) : ℝ) := by
    rw [show (257 / 1600 : ℝ) - Real.pi * Real.exp (513 / 800 : ℝ) =
      -(Real.pi * Real.exp (513 / 800 : ℝ) - (257 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (5972884617044709 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (5972884617044709 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell513_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (513 / 1600 : ℝ) (257 / 800 : ℝ)) :
    (6371263209 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1614184037 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell513_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell513_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell514_leftExp :
    (297066877 / 156250000 : ℝ) ≤ Real.exp (257 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (257 / 400 : ℝ) (1020281046369 / 1000000000000 : ℝ)
    (297066877 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell514_rightExp :
    Real.exp (103 / 160 : ℝ) ≤ (951803017 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (103 / 160 : ℝ) (1020320901877 / 1000000000000 : ℝ)
    (951803017 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell514_denomUpper :
    Real.exp (2909865195586081 / 500000000000000 : ℝ) ≤ (1684406076197 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (2909865195586081 / 500000000000000 : ℝ) (1199454145703 /
    1000000000000 : ℝ) (1684406076197 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell514_denomLower :
    (3342687182557 / 10000000000 : ℝ) ≤ Real.exp (28378638746037 / 4882812500000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (28378638746037 / 4882812500000 : ℝ) (149895296237 /
    125000000000 : ℝ) (3342687182557 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell514_product_lower :
    (116657865531023 / 19531250000000 : ℝ) ≤ Real.pi * Real.exp (257 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell514_leftExp
    (by norm_num : (0 : ℝ) ≤ (297066877 / 156250000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell514_product_upper :
    Real.pi * Real.exp (103 / 160 : ℝ) ≤ (2990177695586081 / 500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell514_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell514_endpointLower :
    (6344314291 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (257 / 800 : ℝ) (103 / 320 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (116657865531023 / 19531250000000 : ℝ) (Real.pi * Real.exp (257 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell514_product_lower
  have hD : Real.exp (Real.pi * Real.exp (103 / 160 : ℝ) - (257 / 1600 : ℝ)) ≤
      (1684406076197 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell514_denomUpper
    linarith [hpThetaJensenCell514_product_upper]
  have hi : (1 / (1684406076197 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (103 / 160 : ℝ) - (257 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1684406076197 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1684406076197 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((257 / 1600 : ℝ) - Real.pi * Real.exp (103 / 160 : ℝ)) := by
    rw [show (257 / 1600 : ℝ) - Real.pi * Real.exp (103 / 160 : ℝ) =
      -(Real.pi * Real.exp (103 / 160 : ℝ) - (257 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (257 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (257 / 400 : ℝ)) := by
    have h := hpThetaJensenCell514_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1684406076197 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell514_endpointUpper :
    hpThetaJensenKernelEndpointUpper (257 / 800 : ℝ) (103 / 320 : ℝ) ≤ (321474061 / 500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (103 / 160 : ℝ)) (2990177695586081 / 500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (103 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell514_product_upper
  have hD : (3342687182557 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (257 / 400 : ℝ) - (103 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell514_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell514_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (257 / 400 : ℝ) - (103 / 640 : ℝ)) ≤
      (1 / (3342687182557 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3342687182557 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((103 / 640 : ℝ) - Real.pi * Real.exp (257 / 400 : ℝ)) ≤
      (2 / (3342687182557 / 10000000000 : ℝ) : ℝ) := by
    rw [show (103 / 640 : ℝ) - Real.pi * Real.exp (257 / 400 : ℝ) =
      -(Real.pi * Real.exp (257 / 400 : ℝ) - (103 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2990177695586081 / 500000000000000 : ℝ) ^ 2 - 6 *
      (2990177695586081 / 500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell514_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (257 / 800 : ℝ) (103 / 320 : ℝ)) :
    (6344314291 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (321474061 / 500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell514_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell514_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell515_leftExp :
    (9518030169 / 5000000000 : ℝ) ≤ Real.exp (103 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (103 / 160 : ℝ) (255080225469 / 250000000000 : ℝ)
    (9518030169 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell515_rightExp :
    Real.exp (129 / 200 : ℝ) ≤ (9529935147 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (129 / 200 : ℝ) (1020360758941 / 1000000000000 : ℝ)
    (9529935147 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell515_denomUpper :
    Real.exp (29134490048269171 / 5000000000000000 : ℝ) ≤ (3393045255697 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (29134490048269171 / 5000000000000000 : ℝ) (599861419611
    / 500000000000 : ℝ) (3393045255697 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell515_denomLower :
    (3366700891541 / 10000000000 : ℝ) ≤ Real.exp (3636939679336131 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3636939679336131 / 625000000000000 : ℝ) (1199430647717 /
    1000000000000 : ℝ) (3366700891541 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell515_product_lower :
    (3737720929336131 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (103 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell515_leftExp
    (by norm_num : (0 : ℝ) ≤ (9518030169 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell515_product_upper :
    Real.pi * Real.exp (129 / 200 : ℝ) ≤ (29939177548269171 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell515_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell515_endpointLower :
    (6317415909 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (103 / 320 : ℝ) (129 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3737720929336131 / 625000000000000 : ℝ) (Real.pi * Real.exp (103 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell515_product_lower
  have hD : Real.exp (Real.pi * Real.exp (129 / 200 : ℝ) - (103 / 640 : ℝ)) ≤
      (3393045255697 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell515_denomUpper
    linarith [hpThetaJensenCell515_product_upper]
  have hi : (1 / (3393045255697 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (129 / 200 : ℝ) - (103 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3393045255697 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3393045255697 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((103 / 640 : ℝ) - Real.pi * Real.exp (129 / 200 : ℝ)) := by
    rw [show (103 / 640 : ℝ) - Real.pi * Real.exp (129 / 200 : ℝ) =
      -(Real.pi * Real.exp (129 / 200 : ℝ) - (103 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (103 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (103 / 160 : ℝ)) := by
    have h := hpThetaJensenCell515_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3393045255697 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell515_endpointUpper :
    hpThetaJensenKernelEndpointUpper (103 / 320 : ℝ) (129 / 400 : ℝ) ≤ (6402277119 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (129 / 200 : ℝ)) (29939177548269171 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (129 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell515_product_upper
  have hD : (3366700891541 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (103 / 160 : ℝ) - (129 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell515_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell515_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (103 / 160 : ℝ) - (129 / 800 : ℝ)) ≤
      (1 / (3366700891541 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3366700891541 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((129 / 800 : ℝ) - Real.pi * Real.exp (103 / 160 : ℝ)) ≤
      (2 / (3366700891541 / 10000000000 : ℝ) : ℝ) := by
    rw [show (129 / 800 : ℝ) - Real.pi * Real.exp (103 / 160 : ℝ) =
      -(Real.pi * Real.exp (103 / 160 : ℝ) - (129 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (29939177548269171 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (29939177548269171 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell515_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (103 / 320 : ℝ) (129 / 400 : ℝ)) :
    (6317415909 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6402277119 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell515_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell515_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell516_leftExp :
    (4764967573 / 2500000000 : ℝ) ≤ Real.exp (129 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (129 / 200 : ℝ) (51018037947 / 50000000000 : ℝ)
    (4764967573 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell516_rightExp :
    Real.exp (517 / 800 : ℝ) ≤ (4770927507 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (517 / 800 : ℝ) (510200308781 / 500000000000 : ℝ)
    (4770927507 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell516_denomUpper :
    Real.exp (14585187459498651 / 2500000000000000 : ℝ) ≤ (3417484649313 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (14585187459498651 / 2500000000000000 : ℝ) (1199991943767
    / 1000000000000 : ℝ) (3417484649313 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell516_denomLower :
    (1695459399853 / 5000000000 : ℝ) ≤ Real.exp (1820709719699527 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1820709719699527 / 312500000000000 : ℝ) (1199699335883 /
    1000000000000 : ℝ) (1695459399853 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell516_product_lower :
    (1871198000949527 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (129 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell516_leftExp
    (by norm_num : (0 : ℝ) ≤ (4764967573 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell516_product_upper :
    Real.pi * Real.exp (517 / 800 : ℝ) ≤ (14988312459498651 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell516_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell516_endpointLower :
    (6290568323 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (129 / 400 : ℝ) (517 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1871198000949527 / 312500000000000 : ℝ) (Real.pi * Real.exp (129 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell516_product_lower
  have hD : Real.exp (Real.pi * Real.exp (517 / 800 : ℝ) - (129 / 800 : ℝ)) ≤
      (3417484649313 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell516_denomUpper
    linarith [hpThetaJensenCell516_product_upper]
  have hi : (1 / (3417484649313 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (517 / 800 : ℝ) - (129 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3417484649313 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3417484649313 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((129 / 800 : ℝ) - Real.pi * Real.exp (517 / 800 : ℝ)) := by
    rw [show (129 / 800 : ℝ) - Real.pi * Real.exp (517 / 800 : ℝ) =
      -(Real.pi * Real.exp (517 / 800 : ℝ) - (129 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (129 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (129 / 200 : ℝ)) := by
    have h := hpThetaJensenCell516_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3417484649313 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell516_endpointUpper :
    hpThetaJensenKernelEndpointUpper (129 / 400 : ℝ) (517 / 1600 : ℝ) ≤ (6375124107 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (517 / 800 : ℝ)) (14988312459498651 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (517 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell516_product_upper
  have hD : (1695459399853 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (129 / 200 : ℝ) - (517 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell516_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell516_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (129 / 200 : ℝ) - (517 / 3200 : ℝ)) ≤
      (1 / (1695459399853 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1695459399853 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((517 / 3200 : ℝ) - Real.pi * Real.exp (129 / 200 : ℝ)) ≤
      (2 / (1695459399853 / 5000000000 : ℝ) : ℝ) := by
    rw [show (517 / 3200 : ℝ) - Real.pi * Real.exp (129 / 200 : ℝ) =
      -(Real.pi * Real.exp (129 / 200 : ℝ) - (517 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (14988312459498651 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (14988312459498651 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell516_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (129 / 400 : ℝ) (517 / 1600 : ℝ)) :
    (6290568323 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6375124107 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell516_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell516_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell517_leftExp :
    (19083710027 / 10000000000 : ℝ) ≤ Real.exp (517 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (517 / 800 : ℝ) (1020400617561 / 1000000000000 : ℝ)
    (19083710027 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell517_rightExp :
    Real.exp (259 / 400 : ℝ) ≤ (19107579581 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (259 / 400 : ℝ) (1020440477739 / 1000000000000 : ℝ)
    (19107579581 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell517_denomUpper :
    Real.exp (58412613258612533 / 10000000000000000 : ℝ) ≤ (3442132320213 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (58412613258612533 / 10000000000000000 : ℝ)
    (1200261460047 / 1000000000000 : ℝ) (3442132320213 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell517_denomLower :
    (1707671434943 / 5000000000 : ℝ) ≤ Real.exp (7291810093892873 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7291810093892873 / 1250000000000000 : ℝ) (1199968435079
    / 1000000000000 : ℝ) (1707671434943 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell517_product_lower :
    (7494153843892873 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (517 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell517_leftExp
    (by norm_num : (0 : ℝ) ≤ (19083710027 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell517_product_upper :
    Real.pi * Real.exp (259 / 400 : ℝ) ≤ (60028238258612533 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell517_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell517_endpointLower :
    (6263771791 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (517 / 1600 : ℝ) (259 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7494153843892873 / 1250000000000000 : ℝ) (Real.pi * Real.exp (517 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell517_product_lower
  have hD : Real.exp (Real.pi * Real.exp (259 / 400 : ℝ) - (517 / 3200 : ℝ)) ≤
      (3442132320213 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell517_denomUpper
    linarith [hpThetaJensenCell517_product_upper]
  have hi : (1 / (3442132320213 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (259 / 400 : ℝ) - (517 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3442132320213 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3442132320213 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((517 / 3200 : ℝ) - Real.pi * Real.exp (259 / 400 : ℝ)) := by
    rw [show (517 / 3200 : ℝ) - Real.pi * Real.exp (259 / 400 : ℝ) =
      -(Real.pi * Real.exp (259 / 400 : ℝ) - (517 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (517 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (517 / 800 : ℝ)) := by
    have h := hpThetaJensenCell517_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3442132320213 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell517_endpointUpper :
    hpThetaJensenKernelEndpointUpper (517 / 1600 : ℝ) (259 / 800 : ℝ) ≤ (6348022449 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (259 / 400 : ℝ)) (60028238258612533 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (259 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell517_product_upper
  have hD : (1707671434943 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (517 / 800 : ℝ) - (259 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell517_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell517_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (517 / 800 : ℝ) - (259 / 1600 : ℝ)) ≤
      (1 / (1707671434943 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1707671434943 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((259 / 1600 : ℝ) - Real.pi * Real.exp (517 / 800 : ℝ)) ≤
      (2 / (1707671434943 / 5000000000 : ℝ) : ℝ) := by
    rw [show (259 / 1600 : ℝ) - Real.pi * Real.exp (517 / 800 : ℝ) =
      -(Real.pi * Real.exp (517 / 800 : ℝ) - (259 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (60028238258612533 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (60028238258612533 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell517_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (517 / 1600 : ℝ) (259 / 800 : ℝ)) :
    (6263771791 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6348022449 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell517_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell517_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell518_leftExp :
    (19107579579 / 10000000000 : ℝ) ≤ Real.exp (259 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (259 / 400 : ℝ) (510220238869 / 500000000000 : ℝ)
    (19107579579 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell518_rightExp :
    Real.exp (519 / 800 : ℝ) ≤ (1913147899 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (519 / 800 : ℝ) (510240169737 / 500000000000 : ℝ)
    (1913147899 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell518_denomUpper :
    Real.exp (5848457047463107 / 1000000000000000 : ℝ) ≤ (86674756859 / 250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (5848457047463107 / 1000000000000000 : ℝ) (1200531388749
    / 1000000000000 : ℝ) (86674756859 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell518_denomLower :
    (859993771109 / 2500000000 : ℝ) ≤ Real.exp (7300793018093721 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7300793018093721 / 1250000000000000 : ℝ) (1200237945977
    / 1000000000000 : ℝ) (859993771109 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell518_product_lower :
    (7503527393093721 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (259 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell518_leftExp
    (by norm_num : (0 : ℝ) ≤ (19107579579 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell518_product_upper :
    Real.pi * Real.exp (519 / 800 : ℝ) ≤ (6010332047463107 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell518_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell518_endpointLower :
    (6237026567 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (259 / 800 : ℝ) (519 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7503527393093721 / 1250000000000000 : ℝ) (Real.pi * Real.exp (259 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell518_product_lower
  have hD : Real.exp (Real.pi * Real.exp (519 / 800 : ℝ) - (259 / 1600 : ℝ)) ≤
      (86674756859 / 250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell518_denomUpper
    linarith [hpThetaJensenCell518_product_upper]
  have hi : (1 / (86674756859 / 250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (519 / 800 : ℝ) - (259 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (86674756859 / 250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (86674756859 / 250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((259 / 1600 : ℝ) - Real.pi * Real.exp (519 / 800 : ℝ)) := by
    rw [show (259 / 1600 : ℝ) - Real.pi * Real.exp (519 / 800 : ℝ) =
      -(Real.pi * Real.exp (519 / 800 : ℝ) - (259 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (259 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (259 / 400 : ℝ)) := by
    have h := hpThetaJensenCell518_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (86674756859 / 250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell518_endpointUpper :
    hpThetaJensenKernelEndpointUpper (259 / 800 : ℝ) (519 / 1600 : ℝ) ≤ (6320972409 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (519 / 800 : ℝ)) (6010332047463107 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (519 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell518_product_upper
  have hD : (859993771109 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (259 / 400 : ℝ) - (519 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell518_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell518_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (259 / 400 : ℝ) - (519 / 3200 : ℝ)) ≤
      (1 / (859993771109 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (859993771109 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((519 / 3200 : ℝ) - Real.pi * Real.exp (259 / 400 : ℝ)) ≤
      (2 / (859993771109 / 2500000000 : ℝ) : ℝ) := by
    rw [show (519 / 3200 : ℝ) - Real.pi * Real.exp (259 / 400 : ℝ) =
      -(Real.pi * Real.exp (259 / 400 : ℝ) - (519 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (6010332047463107 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (6010332047463107 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell518_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (259 / 800 : ℝ) (519 / 1600 : ℝ)) :
    (6237026567 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6320972409 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell518_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell518_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell519_leftExp :
    (4782869747 / 2500000000 : ℝ) ≤ Real.exp (519 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (519 / 800 : ℝ) (1020480339473 / 1000000000000 : ℝ)
    (4782869747 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell519_rightExp :
    Real.exp (13 / 20 : ℝ) ≤ (19155408291 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (13 / 20 : ℝ) (510260101383 / 500000000000 : ℝ)
    (19155408291 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell519_denomUpper :
    Real.exp (58556621599147563 / 10000000000000000 : ℝ) ≤ (218253783607 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (58556621599147563 / 10000000000000000 : ℝ)
    (1200801730547 / 1000000000000 : ℝ) (218253783607 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell519_denomLower :
    (346481745143 / 1000000000 : ℝ) ≤ Real.exp (1827446916777153 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1827446916777153 / 312500000000000 : ℝ) (1200507869301 /
    1000000000000 : ℝ) (346481745143 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell519_product_lower :
    (1878228166777153 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (519 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell519_leftExp
    (by norm_num : (0 : ℝ) ≤ (4782869747 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell519_product_upper :
    Real.pi * Real.exp (13 / 20 : ℝ) ≤ (60178496599147563 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell519_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell519_endpointLower :
    (6210332913 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (519 / 1600 : ℝ) (13 / 40 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1878228166777153 / 312500000000000 : ℝ) (Real.pi * Real.exp (519 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell519_product_lower
  have hD : Real.exp (Real.pi * Real.exp (13 / 20 : ℝ) - (519 / 3200 : ℝ)) ≤
      (218253783607 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell519_denomUpper
    linarith [hpThetaJensenCell519_product_upper]
  have hi : (1 / (218253783607 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (13 / 20 : ℝ) - (519 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (218253783607 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (218253783607 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((519 / 3200 : ℝ) - Real.pi * Real.exp (13 / 20 : ℝ)) := by
    rw [show (519 / 3200 : ℝ) - Real.pi * Real.exp (13 / 20 : ℝ) =
      -(Real.pi * Real.exp (13 / 20 : ℝ) - (519 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (519 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (519 / 800 : ℝ)) := by
    have h := hpThetaJensenCell519_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (218253783607 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell519_endpointUpper :
    hpThetaJensenKernelEndpointUpper (519 / 1600 : ℝ) (13 / 40 : ℝ) ≤ (6293974237 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (13 / 20 : ℝ)) (60178496599147563 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (13 / 40 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell519_product_upper
  have hD : (346481745143 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (519 / 800 : ℝ) - (13 / 80 : ℝ)) := by
    apply le_trans hpThetaJensenCell519_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell519_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (519 / 800 : ℝ) - (13 / 80 : ℝ)) ≤
      (1 / (346481745143 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (346481745143 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((13 / 80 : ℝ) - Real.pi * Real.exp (519 / 800 : ℝ)) ≤
      (2 / (346481745143 / 1000000000 : ℝ) : ℝ) := by
    rw [show (13 / 80 : ℝ) - Real.pi * Real.exp (519 / 800 : ℝ) =
      -(Real.pi * Real.exp (519 / 800 : ℝ) - (13 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (60178496599147563 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (60178496599147563 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell519_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (519 / 1600 : ℝ) (13 / 40 : ℝ)) :
    (6210332913 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6293974237 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell519_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell519_endpointUpper

def hpThetaJensenCellsBatch025Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (26904303 / 40000000 : ℝ)
  | 1 => (6698494463 / 10000000000 : ℝ)
  | 2 => (6670960151 / 10000000000 : ℝ)
  | 3 => (830434137 / 1250000000 : ℝ)
  | 4 => (1323206717 / 2000000000 : ℝ)
  | 5 => (3294320949 / 5000000000 : ℝ)
  | 6 => (6561298313 / 10000000000 : ℝ)
  | 7 => (653400311 / 1000000000 : ℝ)
  | 8 => (3253378281 / 5000000000 : ℝ)
  | 9 => (3239779473 / 5000000000 : ℝ)
  | 10 => (1290482107 / 2000000000 : ℝ)
  | 11 => (1285062319 / 2000000000 : ℝ)
  | 12 => (6398262399 / 10000000000 : ℝ)
  | 13 => (6371263209 / 10000000000 : ℝ)
  | 14 => (6344314291 / 10000000000 : ℝ)
  | 15 => (6317415909 / 10000000000 : ℝ)
  | 16 => (6290568323 / 10000000000 : ℝ)
  | 17 => (6263771791 / 10000000000 : ℝ)
  | 18 => (6237026567 / 10000000000 : ℝ)
  | 19 => (6210332913 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch025Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (6815551617 / 10000000000 : ℝ)
  | 1 => (84845761 / 125000000 : ℝ)
  | 2 => (3379908679 / 5000000000 : ℝ)
  | 3 => (3366010671 / 5000000000 : ℝ)
  | 4 => (6704273113 / 10000000000 : ℝ)
  | 5 => (6676572963 / 10000000000 : ℝ)
  | 6 => (1662230293 / 2500000000 : ℝ)
  | 7 => (3310659011 / 5000000000 : ℝ)
  | 8 => (6593763797 / 10000000000 : ℝ)
  | 9 => (656625877 / 1000000000 : ℝ)
  | 10 => (3269401609 / 5000000000 : ℝ)
  | 11 => (813924677 / 1250000000 : ℝ)
  | 12 => (1621010409 / 2500000000 : ℝ)
  | 13 => (1614184037 / 2500000000 : ℝ)
  | 14 => (321474061 / 500000000 : ℝ)
  | 15 => (6402277119 / 10000000000 : ℝ)
  | 16 => (6375124107 / 10000000000 : ℝ)
  | 17 => (6348022449 / 10000000000 : ℝ)
  | 18 => (6320972409 / 10000000000 : ℝ)
  | 19 => (6293974237 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch025_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((500 : ℝ) + (j.val : ℝ)) / 1600)
      (((500 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch025Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch025Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell500_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell501_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell502_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell503_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell504_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell505_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell506_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell507_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell508_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell509_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell510_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell511_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell512_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell513_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell514_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell515_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell516_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell517_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell518_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell519_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper] at h ⊢
    exact h

end HodgeProofHP
