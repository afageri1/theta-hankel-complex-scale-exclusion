import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1200_leftExp :
    (22408445351 / 5000000000 : ℝ) ≤ Real.exp (3 / 2 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3 / 2 : ℝ) (32749718813 / 31250000000 : ℝ) (22408445351
    / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1200_rightExp :
    Real.exp (1201 / 800 : ℝ) ≤ (8974589369 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1201 / 800 : ℝ) (209606387993 / 200000000000 : ℝ)
    (8974589369 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1200_denomUpper :
    Real.exp (27444507139524817 / 2000000000000000 : ℝ) ≤ (182191872882289 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (27444507139524817 / 2000000000000000 : ℝ) (767722640301
    / 500000000000 : ℝ) (182191872882289 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1200_denomLower :
    (8947736224166207 / 10000000000 : ℝ) ≤ Real.exp (8565203768392349 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8565203768392349 / 625000000000000 : ℝ) (767292655177 /
    500000000000 : ℝ) (8947736224166207 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1200_product_lower :
    (8799774080892349 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (3 / 2 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1200_leftExp
    (by norm_num : (0 : ℝ) ≤ (22408445351 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1200_product_upper :
    Real.pi * Real.exp (1201 / 800 : ℝ) ≤ (28194507139524817 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1200_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1200_endpointLower :
    (7777153 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (3 / 4 : ℝ) (1201 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8799774080892349 / 625000000000000 : ℝ) (Real.pi * Real.exp (3 / 2 : ℝ))
    (by norm_num) hpThetaJensenCell1200_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1201 / 800 : ℝ) - (3 / 8 : ℝ)) ≤
      (182191872882289 / 200000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1200_denomUpper
    linarith [hpThetaJensenCell1200_product_upper]
  have hi : (1 / (182191872882289 / 200000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1201 / 800 : ℝ) - (3 / 8 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (182191872882289 / 200000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (182191872882289 / 200000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((3 / 8 : ℝ) - Real.pi * Real.exp (1201 / 800 : ℝ)) := by
    rw [show (3 / 8 : ℝ) - Real.pi * Real.exp (1201 / 800 : ℝ) =
      -(Real.pi * Real.exp (1201 / 800 : ℝ) - (3 / 8 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (3 / 2 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (3 / 2 : ℝ)) := by
    have h := hpThetaJensenCell1200_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (182191872882289 / 200000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1200_endpointUpper :
    hpThetaJensenKernelEndpointUpper (3 / 4 : ℝ) (1201 / 1600 : ℝ) ≤ (31839 / 20000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1201 / 800 : ℝ)) (28194507139524817 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1201 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1200_product_upper
  have hD : (8947736224166207 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (3 / 2 : ℝ) - (1201 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1200_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1200_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (3 / 2 : ℝ) - (1201 / 3200 : ℝ)) ≤
      (1 / (8947736224166207 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (8947736224166207 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1201 / 3200 : ℝ) - Real.pi * Real.exp (3 / 2 : ℝ)) ≤
      (2 / (8947736224166207 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1201 / 3200 : ℝ) - Real.pi * Real.exp (3 / 2 : ℝ) =
      -(Real.pi * Real.exp (3 / 2 : ℝ) - (1201 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (28194507139524817 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (28194507139524817 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1200_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (3 / 4 : ℝ) (1201 / 1600 : ℝ)) :
    (7777153 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (31839 / 20000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1200_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1200_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1201_leftExp :
    (44872946843 / 10000000000 : ℝ) ≤ Real.exp (1201 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1201 / 800 : ℝ) (262007984991 / 250000000000 : ℝ)
    (44872946843 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1201_rightExp :
    Real.exp (601 / 400 : ℝ) ≤ (449290731 / 100000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (601 / 400 : ℝ) (131009109939 / 125000000000 : ℝ)
    (449290731 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1201_denomUpper :
    Real.exp (1373957365474483 / 100000000000000 : ℝ) ≤ (9268746875285989 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1373957365474483 / 100000000000000 : ℝ) (768138284693 /
    500000000000 : ℝ) (9268746875285989 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1201_denomLower :
    (2275965267309097 / 2500000000 : ℝ) ≤ Real.exp (17152030102299257 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (17152030102299257 / 1250000000000000 : ℝ) (153541507639
    / 100000000000 : ℝ) (2275965267309097 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1201_product_lower :
    (17621561352299257 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1201 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1201_leftExp
    (by norm_num : (0 : ℝ) ≤ (44872946843 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1201_product_upper :
    Real.pi * Real.exp (601 / 400 : ℝ) ≤ (1411488615474483 / 100000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1201_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1201_endpointLower :
    (3831943 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (1201 / 1600 : ℝ) (601 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (17621561352299257 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1201 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1201_product_lower
  have hD : Real.exp (Real.pi * Real.exp (601 / 400 : ℝ) - (1201 / 3200 : ℝ)) ≤
      (9268746875285989 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1201_denomUpper
    linarith [hpThetaJensenCell1201_product_upper]
  have hi : (1 / (9268746875285989 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (601 / 400 : ℝ) - (1201 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (9268746875285989 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (9268746875285989 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1201 / 3200 : ℝ) - Real.pi * Real.exp (601 / 400 : ℝ)) := by
    rw [show (1201 / 3200 : ℝ) - Real.pi * Real.exp (601 / 400 : ℝ) =
      -(Real.pi * Real.exp (601 / 400 : ℝ) - (1201 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1201 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1201 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1201_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (9268746875285989 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1201_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1201 / 1600 : ℝ) (601 / 800 : ℝ) ≤ (15687991 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (601 / 400 : ℝ)) (1411488615474483 / 100000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (601 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1201_product_upper
  have hD : (2275965267309097 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1201 / 800 : ℝ) - (601 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1201_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1201_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1201 / 800 : ℝ) - (601 / 1600 : ℝ)) ≤
      (1 / (2275965267309097 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2275965267309097 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((601 / 1600 : ℝ) - Real.pi * Real.exp (1201 / 800 : ℝ)) ≤
      (2 / (2275965267309097 / 2500000000 : ℝ) : ℝ) := by
    rw [show (601 / 1600 : ℝ) - Real.pi * Real.exp (1201 / 800 : ℝ) =
      -(Real.pi * Real.exp (1201 / 800 : ℝ) - (601 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1411488615474483 / 100000000000000 : ℝ) ^ 2 - 6 *
      (1411488615474483 / 100000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1201_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1201 / 1600 : ℝ) (601 / 800 : ℝ)) :
    (3831943 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15687991 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1201_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1201_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1202_leftExp :
    (22464536549 / 5000000000 : ℝ) ≤ Real.exp (601 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (601 / 400 : ℝ) (1048072879511 / 1000000000000 : ℝ)
    (22464536549 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1202_rightExp :
    Real.exp (1203 / 800 : ℝ) ≤ (22492634779 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1203 / 800 : ℝ) (1048113820659 / 1000000000000 : ℝ)
    (22492634779 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1202_denomUpper :
    Real.exp (68784578973262947 / 5000000000000000 : ℝ) ≤ (9430888659495629 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (68784578973262947 / 5000000000000000 : ℝ) (153710936763
    / 100000000000 : ℝ) (9430888659495629 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1202_denomLower :
    (9262914094901591 / 10000000000 : ℝ) ≤ Real.exp (8586840100755751 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8586840100755751 / 625000000000000 : ℝ) (192030793569 /
    125000000000 : ℝ) (9262914094901591 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1202_product_lower :
    (8821801038255751 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (601 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1202_leftExp
    (by norm_num : (0 : ℝ) ≤ (22464536549 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1202_product_upper :
    Real.pi * Real.exp (1203 / 800 : ℝ) ≤ (70662703973262947 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1202_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1202_endpointLower :
    (7552101 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (601 / 800 : ℝ) (1203 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8821801038255751 / 625000000000000 : ℝ) (Real.pi * Real.exp (601 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1202_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1203 / 800 : ℝ) - (601 / 1600 : ℝ)) ≤
      (9430888659495629 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1202_denomUpper
    linarith [hpThetaJensenCell1202_product_upper]
  have hi : (1 / (9430888659495629 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1203 / 800 : ℝ) - (601 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (9430888659495629 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (9430888659495629 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((601 / 1600 : ℝ) - Real.pi * Real.exp (1203 / 800 : ℝ)) := by
    rw [show (601 / 1600 : ℝ) - Real.pi * Real.exp (1203 / 800 : ℝ) =
      -(Real.pi * Real.exp (1203 / 800 : ℝ) - (601 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (601 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (601 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1202_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (9430888659495629 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1202_endpointUpper :
    hpThetaJensenKernelEndpointUpper (601 / 800 : ℝ) (1203 / 1600 : ℝ) ≤ (966219 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1203 / 800 : ℝ)) (70662703973262947 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1203 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1202_product_upper
  have hD : (9262914094901591 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (601 / 400 : ℝ) - (1203 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1202_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1202_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (601 / 400 : ℝ) - (1203 / 3200 : ℝ)) ≤
      (1 / (9262914094901591 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (9262914094901591 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1203 / 3200 : ℝ) - Real.pi * Real.exp (601 / 400 : ℝ)) ≤
      (2 / (9262914094901591 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1203 / 3200 : ℝ) - Real.pi * Real.exp (601 / 400 : ℝ) =
      -(Real.pi * Real.exp (601 / 400 : ℝ) - (1203 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (70662703973262947 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (70662703973262947 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1202_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (601 / 800 : ℝ) (1203 / 1600 : ℝ)) :
    (7552101 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (966219 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1202_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1202_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1203_leftExp :
    (8997053911 / 2000000000 : ℝ) ≤ Real.exp (1203 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1203 / 800 : ℝ) (524056910329 / 500000000000 : ℝ)
    (8997053911 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1203_rightExp :
    Real.exp (301 / 200 : ℝ) ≤ (2815096019 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (301 / 200 : ℝ) (209630952681 / 200000000000 : ℝ)
    (2815096019 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1203_denomUpper :
    Real.exp (8608925010118267 / 625000000000000 : ℝ) ≤ (239901968690353 / 250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8608925010118267 / 625000000000000 : ℝ) (192242959823 /
    125000000000 : ℝ) (239901968690353 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1203_denomLower :
    (9424953788173603 / 10000000000 : ℝ) ≤ Real.exp (3439071573795789 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3439071573795789 / 250000000000000 : ℝ) (1537079130129 /
    1000000000000 : ℝ) (9424953788173603 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1203_product_lower :
    (3533134073795789 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1203 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1203_leftExp
    (by norm_num : (0 : ℝ) ≤ (8997053911 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1203_product_upper :
    Real.pi * Real.exp (301 / 200 : ℝ) ≤ (8843885947618267 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1203_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1203_endpointLower :
    (372089 / 250000000 : ℝ) ≤ hpThetaTraceEndpointLower (1203 / 1600 : ℝ) (301 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3533134073795789 / 250000000000000 : ℝ) (Real.pi * Real.exp (1203 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1203_product_lower
  have hD : Real.exp (Real.pi * Real.exp (301 / 200 : ℝ) - (1203 / 3200 : ℝ)) ≤
      (239901968690353 / 250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1203_denomUpper
    linarith [hpThetaJensenCell1203_product_upper]
  have hi : (1 / (239901968690353 / 250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (301 / 200 : ℝ) - (1203 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (239901968690353 / 250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (239901968690353 / 250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1203 / 3200 : ℝ) - Real.pi * Real.exp (301 / 200 : ℝ)) := by
    rw [show (1203 / 3200 : ℝ) - Real.pi * Real.exp (301 / 200 : ℝ) =
      -(Real.pi * Real.exp (301 / 200 : ℝ) - (1203 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1203 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1203 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1203_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (239901968690353 / 250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1203_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1203 / 1600 : ℝ) (301 / 400 : ℝ) ≤ (3046801 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (301 / 200 : ℝ)) (8843885947618267 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (301 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1203_product_upper
  have hD : (9424953788173603 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1203 / 800 : ℝ) - (301 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1203_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1203_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1203 / 800 : ℝ) - (301 / 800 : ℝ)) ≤
      (1 / (9424953788173603 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (9424953788173603 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((301 / 800 : ℝ) - Real.pi * Real.exp (1203 / 800 : ℝ)) ≤
      (2 / (9424953788173603 / 10000000000 : ℝ) : ℝ) := by
    rw [show (301 / 800 : ℝ) - Real.pi * Real.exp (1203 / 800 : ℝ) =
      -(Real.pi * Real.exp (1203 / 800 : ℝ) - (301 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8843885947618267 / 625000000000000 : ℝ) ^ 2 - 6 *
      (8843885947618267 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1203_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1203 / 1600 : ℝ) (301 / 400 : ℝ)) :
    (372089 / 250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3046801 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1203_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1203_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1204_leftExp :
    (22520768151 / 5000000000 : ℝ) ≤ Real.exp (301 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (301 / 200 : ℝ) (262038690851 / 250000000000 : ℝ)
    (22520768151 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1204_rightExp :
    Real.exp (241 / 160 : ℝ) ≤ (11274468357 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (241 / 160 : ℝ) (4192782831 / 4000000000 : ℝ)
    (11274468357 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1204_denomUpper :
    Real.exp (34479165869072701 / 2500000000000000 : ℝ) ≤ (305136817762231 / 312500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (34479165869072701 / 2500000000000000 : ℝ) (1538779505579
    / 1000000000000 : ℝ) (305136817762231 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1204_denomLower :
    (1198754983839329 / 1250000000 : ℝ) ≤ Real.exp (8608531569629549 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8608531569629549 / 625000000000000 : ℝ) (768956712207 /
    500000000000 : ℝ) (1198754983839329 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1204_product_lower :
    (8843883132129549 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (301 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1204_leftExp
    (by norm_num : (0 : ℝ) ≤ (22520768151 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1204_product_upper :
    Real.pi * Real.exp (241 / 160 : ℝ) ≤ (35419790869072701 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1204_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1204_endpointLower :
    (2933163 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (301 / 400 : ℝ) (241 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8843883132129549 / 625000000000000 : ℝ) (Real.pi * Real.exp (301 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1204_product_lower
  have hD : Real.exp (Real.pi * Real.exp (241 / 160 : ℝ) - (301 / 800 : ℝ)) ≤
      (305136817762231 / 312500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1204_denomUpper
    linarith [hpThetaJensenCell1204_product_upper]
  have hi : (1 / (305136817762231 / 312500000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (241 / 160 : ℝ) - (301 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (305136817762231 / 312500000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (305136817762231 / 312500000 : ℝ) : ℝ) ≤
      2 * Real.exp ((301 / 800 : ℝ) - Real.pi * Real.exp (241 / 160 : ℝ)) := by
    rw [show (301 / 800 : ℝ) - Real.pi * Real.exp (241 / 160 : ℝ) =
      -(Real.pi * Real.exp (241 / 160 : ℝ) - (301 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (301 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (301 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1204_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (305136817762231 / 312500000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1204_endpointUpper :
    hpThetaJensenKernelEndpointUpper (301 / 400 : ℝ) (241 / 320 : ℝ) ≤ (7505731 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (241 / 160 : ℝ)) (35419790869072701 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (241 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1204_product_upper
  have hD : (1198754983839329 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (301 / 200 : ℝ) - (241 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1204_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1204_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (301 / 200 : ℝ) - (241 / 640 : ℝ)) ≤
      (1 / (1198754983839329 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1198754983839329 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((241 / 640 : ℝ) - Real.pi * Real.exp (301 / 200 : ℝ)) ≤
      (2 / (1198754983839329 / 1250000000 : ℝ) : ℝ) := by
    rw [show (241 / 640 : ℝ) - Real.pi * Real.exp (301 / 200 : ℝ) =
      -(Real.pi * Real.exp (301 / 200 : ℝ) - (241 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (35419790869072701 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (35419790869072701 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1204_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (301 / 400 : ℝ) (241 / 320 : ℝ)) :
    (2933163 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7505731 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1204_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1204_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1205_leftExp :
    (22548936713 / 5000000000 : ℝ) ≤ Real.exp (241 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (241 / 160 : ℝ) (1048195707749 / 1000000000000 : ℝ)
    (22548936713 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1205_rightExp :
    Real.exp (603 / 400 : ℝ) ≤ (5644285127 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (603 / 400 : ℝ) (524118326847 / 500000000000 : ℝ)
    (5644285127 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1205_denomUpper :
    Real.exp (17261343519987311 / 1250000000000000 : ℝ) ≤ (9935849230734853 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (17261343519987311 / 1250000000000000 : ℝ) (192452106487
    / 125000000000 : ℝ) (9935849230734853 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1205_denomLower :
    (4879116662396419 / 5000000000 : ℝ) ≤ Real.exp (8619398023258387 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8619398023258387 / 625000000000000 : ℝ) (1538749234697 /
    1000000000000 : ℝ) (4879116662396419 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1205_product_lower :
    (8854944898258387 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (241 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1205_leftExp
    (by norm_num : (0 : ℝ) ≤ (22548936713 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1205_product_upper :
    Real.pi * Real.exp (603 / 400 : ℝ) ≤ (17732046644987311 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1205_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1205_endpointLower :
    (3612733 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (241 / 320 : ℝ) (603 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8854944898258387 / 625000000000000 : ℝ) (Real.pi * Real.exp (241 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1205_product_lower
  have hD : Real.exp (Real.pi * Real.exp (603 / 400 : ℝ) - (241 / 640 : ℝ)) ≤
      (9935849230734853 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1205_denomUpper
    linarith [hpThetaJensenCell1205_product_upper]
  have hi : (1 / (9935849230734853 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (603 / 400 : ℝ) - (241 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (9935849230734853 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (9935849230734853 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((241 / 640 : ℝ) - Real.pi * Real.exp (603 / 400 : ℝ)) := by
    rw [show (241 / 640 : ℝ) - Real.pi * Real.exp (603 / 400 : ℝ) =
      -(Real.pi * Real.exp (603 / 400 : ℝ) - (241 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (241 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (241 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1205_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (9935849230734853 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1205_endpointUpper :
    hpThetaJensenKernelEndpointUpper (241 / 320 : ℝ) (603 / 800 : ℝ) ≤ (14791839 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (603 / 400 : ℝ)) (17732046644987311 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (603 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1205_product_upper
  have hD : (4879116662396419 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (241 / 160 : ℝ) - (603 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1205_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1205_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (241 / 160 : ℝ) - (603 / 1600 : ℝ)) ≤
      (1 / (4879116662396419 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4879116662396419 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((603 / 1600 : ℝ) - Real.pi * Real.exp (241 / 160 : ℝ)) ≤
      (2 / (4879116662396419 / 5000000000 : ℝ) : ℝ) := by
    rw [show (603 / 1600 : ℝ) - Real.pi * Real.exp (241 / 160 : ℝ) =
      -(Real.pi * Real.exp (241 / 160 : ℝ) - (603 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (17732046644987311 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (17732046644987311 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1205_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (241 / 320 : ℝ) (603 / 800 : ℝ)) :
    (3612733 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (14791839 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1205_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1205_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1206_leftExp :
    (22577140507 / 5000000000 : ℝ) ≤ Real.exp (603 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (603 / 400 : ℝ) (1048236653693 / 1000000000000 : ℝ)
    (22577140507 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1206_rightExp :
    Real.exp (1207 / 800 : ℝ) ≤ (45210759159 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1207 / 800 : ℝ) (524138800619 / 500000000000 : ℝ)
    (45210759159 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1206_denomUpper :
    Real.exp (138265054498600287 / 10000000000000000 : ℝ) ≤ (315954861829773 / 312500000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (138265054498600287 / 10000000000000000 : ℝ)
    (308091144179 / 200000000000 : ℝ) (315954861829773 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1206_denomLower :
    (9929596422203917 / 10000000000 : ℝ) ≤ Real.exp (8630278312458393 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8630278312458393 / 625000000000000 : ℝ) (153958656427 /
    100000000000 : ℝ) (9929596422203917 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1206_product_lower :
    (8866020499958393 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (603 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1206_leftExp
    (by norm_num : (0 : ℝ) ≤ (22577140507 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1206_product_upper :
    Real.pi * Real.exp (1207 / 800 : ℝ) ≤ (142033804498600287 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1206_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1206_endpointLower :
    (14238879 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (603 / 800 : ℝ) (1207 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8866020499958393 / 625000000000000 : ℝ) (Real.pi * Real.exp (603 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1206_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1207 / 800 : ℝ) - (603 / 1600 : ℝ)) ≤
      (315954861829773 / 312500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1206_denomUpper
    linarith [hpThetaJensenCell1206_product_upper]
  have hi : (1 / (315954861829773 / 312500000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1207 / 800 : ℝ) - (603 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (315954861829773 / 312500000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (315954861829773 / 312500000 : ℝ) : ℝ) ≤
      2 * Real.exp ((603 / 1600 : ℝ) - Real.pi * Real.exp (1207 / 800 : ℝ)) := by
    rw [show (603 / 1600 : ℝ) - Real.pi * Real.exp (1207 / 800 : ℝ) =
      -(Real.pi * Real.exp (1207 / 800 : ℝ) - (603 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (603 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (603 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1206_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (315954861829773 / 312500000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1206_endpointUpper :
    hpThetaJensenKernelEndpointUpper (603 / 800 : ℝ) (1207 / 1600 : ℝ) ≤ (28467 / 19531250 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1207 / 800 : ℝ)) (142033804498600287 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1207 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1206_product_upper
  have hD : (9929596422203917 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (603 / 400 : ℝ) - (1207 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1206_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1206_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (603 / 400 : ℝ) - (1207 / 3200 : ℝ)) ≤
      (1 / (9929596422203917 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (9929596422203917 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1207 / 3200 : ℝ) - Real.pi * Real.exp (603 / 400 : ℝ)) ≤
      (2 / (9929596422203917 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1207 / 3200 : ℝ) - Real.pi * Real.exp (603 / 400 : ℝ) =
      -(Real.pi * Real.exp (603 / 400 : ℝ) - (1207 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (142033804498600287 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (142033804498600287 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1206_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (603 / 800 : ℝ) (1207 / 1600 : ℝ)) :
    (14238879 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (28467 / 19531250 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1206_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1206_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1207_leftExp :
    (45210759157 / 10000000000 : ℝ) ≤ Real.exp (1207 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1207 / 800 : ℝ) (1048277601237 / 1000000000000 : ℝ)
    (45210759157 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1207_rightExp :
    Real.exp (151 / 100 : ℝ) ≤ (5658413493 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (151 / 100 : ℝ) (524159275191 / 500000000000 : ℝ)
    (5658413493 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1207_denomUpper :
    Real.exp (17304947845714349 / 1250000000000000 : ℝ) ≤ (2057712438817259 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (17304947845714349 / 1250000000000000 : ℝ) (1541296115887
    / 1000000000000 : ℝ) (2057712438817259 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1207_denomLower :
    (10104192767164813 / 10000000000 : ℝ) ≤ Real.exp (17282344910194743 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (17282344910194743 / 1250000000000000 : ℝ) (308085083299
    / 200000000000 : ℝ) (10104192767164813 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1207_product_lower :
    (17754219910194743 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1207 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1207_leftExp
    (by norm_num : (0 : ℝ) ≤ (45210759157 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1207_product_upper :
    Real.pi * Real.exp (151 / 100 : ℝ) ≤ (17776432220714349 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1207_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1207_endpointLower :
    (1753703 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (1207 / 1600 : ℝ) (151 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (17754219910194743 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1207 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1207_product_lower
  have hD : Real.exp (Real.pi * Real.exp (151 / 100 : ℝ) - (1207 / 3200 : ℝ)) ≤
      (2057712438817259 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1207_denomUpper
    linarith [hpThetaJensenCell1207_product_upper]
  have hi : (1 / (2057712438817259 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (151 / 100 : ℝ) - (1207 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2057712438817259 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2057712438817259 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1207 / 3200 : ℝ) - Real.pi * Real.exp (151 / 100 : ℝ)) := by
    rw [show (1207 / 3200 : ℝ) - Real.pi * Real.exp (151 / 100 : ℝ) =
      -(Real.pi * Real.exp (151 / 100 : ℝ) - (1207 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1207 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1207 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1207_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2057712438817259 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1207_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1207 / 1600 : ℝ) (151 / 200 : ℝ) ≤ (14361223 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (151 / 100 : ℝ)) (17776432220714349 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (151 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1207_product_upper
  have hD : (10104192767164813 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1207 / 800 : ℝ) - (151 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1207_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1207_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1207 / 800 : ℝ) - (151 / 400 : ℝ)) ≤
      (1 / (10104192767164813 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (10104192767164813 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((151 / 400 : ℝ) - Real.pi * Real.exp (1207 / 800 : ℝ)) ≤
      (2 / (10104192767164813 / 10000000000 : ℝ) : ℝ) := by
    rw [show (151 / 400 : ℝ) - Real.pi * Real.exp (1207 / 800 : ℝ) =
      -(Real.pi * Real.exp (1207 / 800 : ℝ) - (151 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (17776432220714349 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (17776432220714349 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1207_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1207 / 1600 : ℝ) (151 / 200 : ℝ)) :
    (1753703 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (14361223 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1207_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1207_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1208_leftExp :
    (22633653971 / 5000000000 : ℝ) ≤ Real.exp (151 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (151 / 100 : ℝ) (1048318550381 / 1000000000000 : ℝ)
    (22633653971 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1208_rightExp :
    Real.exp (1209 / 800 : ℝ) ≤ (45323927459 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1209 / 800 : ℝ) (8386876009 / 8000000000 : ℝ)
    (45323927459 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1208_denomUpper :
    Real.exp (138614333237702187 / 10000000000000000 : ℝ) ≤ (10469935441344031 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (138614333237702187 / 10000000000000000 : ℝ) (7710690201
    / 5000000000 : ℝ) (10469935441344031 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1208_denomLower :
    (5141043650385031 / 5000000000 : ℝ) ≤ Real.exp (8652080468257729 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8652080468257729 / 625000000000000 : ℝ) (770632897341 /
    500000000000 : ℝ) (5141043650385031 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1208_product_lower :
    (8888213280757729 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (151 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1208_leftExp
    (by norm_num : (0 : ℝ) ≤ (22633653971 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1208_product_upper :
    Real.pi * Real.exp (1209 / 800 : ℝ) ≤ (142389333237702187 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1208_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1208_endpointLower :
    (13823133 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (151 / 200 : ℝ) (1209 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8888213280757729 / 625000000000000 : ℝ) (Real.pi * Real.exp (151 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1208_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1209 / 800 : ℝ) - (151 / 400 : ℝ)) ≤
      (10469935441344031 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1208_denomUpper
    linarith [hpThetaJensenCell1208_product_upper]
  have hi : (1 / (10469935441344031 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1209 / 800 : ℝ) - (151 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (10469935441344031 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (10469935441344031 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((151 / 400 : ℝ) - Real.pi * Real.exp (1209 / 800 : ℝ)) := by
    rw [show (151 / 400 : ℝ) - Real.pi * Real.exp (1209 / 800 : ℝ) =
      -(Real.pi * Real.exp (1209 / 800 : ℝ) - (151 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (151 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (151 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1208_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (10469935441344031 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1208_endpointUpper :
    hpThetaJensenKernelEndpointUpper (151 / 200 : ℝ) (1209 / 1600 : ℝ) ≤ (3537541 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1209 / 800 : ℝ)) (142389333237702187 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1209 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1208_product_upper
  have hD : (5141043650385031 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (151 / 100 : ℝ) - (1209 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1208_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1208_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (151 / 100 : ℝ) - (1209 / 3200 : ℝ)) ≤
      (1 / (5141043650385031 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5141043650385031 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1209 / 3200 : ℝ) - Real.pi * Real.exp (151 / 100 : ℝ)) ≤
      (2 / (5141043650385031 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1209 / 3200 : ℝ) - Real.pi * Real.exp (151 / 100 : ℝ) =
      -(Real.pi * Real.exp (151 / 100 : ℝ) - (1209 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (142389333237702187 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (142389333237702187 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1208_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (151 / 200 : ℝ) (1209 / 1600 : ℝ)) :
    (13823133 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3537541 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1208_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1208_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1209_leftExp :
    (1416372733 / 312500000 : ℝ) ≤ Real.exp (1209 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1209 / 800 : ℝ) (262089875281 / 250000000000 : ℝ)
    (1416372733 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1209_rightExp :
    Real.exp (121 / 80 : ℝ) ≤ (709072153 / 156250000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (121 / 80 : ℝ) (262100113367 / 250000000000 : ℝ)
    (709072153 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1209_denomUpper :
    Real.exp (2168582909234729 / 156250000000000 : ℝ) ≤ (10654743095964299 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (2168582909234729 / 156250000000000 : ℝ) (771490748587 /
    500000000000 : ℝ) (10654743095964299 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1209_denomLower :
    (2092669268391443 / 2000000000 : ℝ) ≤ Real.exp (541437648063867 / 39062500000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (541437648063867 / 39062500000000 : ℝ) (12047716423 /
    7812500000 : ℝ) (2092669268391443 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1209_product_lower :
    (556208155876367 / 39062500000000 : ℝ) ≤ Real.pi * Real.exp (1209 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1209_leftExp
    (by norm_num : (0 : ℝ) ≤ (1416372733 / 312500000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1209_product_upper :
    Real.pi * Real.exp (121 / 80 : ℝ) ≤ (2227616112359729 / 156250000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1209_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1209_endpointLower :
    (851211 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (1209 / 1600 : ℝ) (121 / 160 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (556208155876367 / 39062500000000 : ℝ) (Real.pi * Real.exp (1209 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1209_product_lower
  have hD : Real.exp (Real.pi * Real.exp (121 / 80 : ℝ) - (1209 / 3200 : ℝ)) ≤
      (10654743095964299 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1209_denomUpper
    linarith [hpThetaJensenCell1209_product_upper]
  have hi : (1 / (10654743095964299 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (121 / 80 : ℝ) - (1209 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (10654743095964299 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (10654743095964299 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1209 / 3200 : ℝ) - Real.pi * Real.exp (121 / 80 : ℝ)) := by
    rw [show (1209 / 3200 : ℝ) - Real.pi * Real.exp (121 / 80 : ℝ) =
      -(Real.pi * Real.exp (121 / 80 : ℝ) - (1209 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1209 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1209 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1209_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (10654743095964299 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1209_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1209 / 1600 : ℝ) (121 / 160 : ℝ) ≤ (13941893 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (121 / 80 : ℝ)) (2227616112359729 / 156250000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (121 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1209_product_upper
  have hD : (2092669268391443 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1209 / 800 : ℝ) - (121 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell1209_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1209_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1209 / 800 : ℝ) - (121 / 320 : ℝ)) ≤
      (1 / (2092669268391443 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2092669268391443 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((121 / 320 : ℝ) - Real.pi * Real.exp (1209 / 800 : ℝ)) ≤
      (2 / (2092669268391443 / 2000000000 : ℝ) : ℝ) := by
    rw [show (121 / 320 : ℝ) - Real.pi * Real.exp (1209 / 800 : ℝ) =
      -(Real.pi * Real.exp (1209 / 800 : ℝ) - (121 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2227616112359729 / 156250000000000 : ℝ) ^ 2 - 6 *
      (2227616112359729 / 156250000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1209_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1209 / 1600 : ℝ) (121 / 160 : ℝ)) :
    (851211 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (13941893 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1209_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1209_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1210_leftExp :
    (4538061779 / 1000000000 : ℝ) ≤ Real.exp (121 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (121 / 80 : ℝ) (1048400453467 / 1000000000000 : ℝ)
    (4538061779 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1210_rightExp :
    Real.exp (1211 / 800 : ℝ) ≤ (22718689517 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1211 / 800 : ℝ) (1048441407411 / 1000000000000 : ℝ)
    (22718689517 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1210_denomUpper :
    Real.exp (69482250955780581 / 5000000000000000 : ℝ) ≤ (542152719267871 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (69482250955780581 / 5000000000000000 : ℝ) (1543826490199
    / 1000000000000 : ℝ) (542152719267871 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1210_denomLower :
    (10648037633652763 / 10000000000 : ℝ) ≤ Real.exp (1734787635051521 / 125000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (1734787635051521 / 125000000000000 : ℝ) (1542951142267 /
    1000000000000 : ℝ) (10648037633652763 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1210_product_lower :
    (1782092322551521 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (121 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1210_leftExp
    (by norm_num : (0 : ℝ) ≤ (4538061779 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1210_product_upper :
    Real.pi * Real.exp (1211 / 800 : ℝ) ≤ (71372875955780581 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1210_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1210_endpointLower :
    (13418321 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (121 / 160 : ℝ) (1211 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1782092322551521 / 125000000000000 : ℝ) (Real.pi * Real.exp (121 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell1210_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1211 / 800 : ℝ) - (121 / 320 : ℝ)) ≤
      (542152719267871 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1210_denomUpper
    linarith [hpThetaJensenCell1210_product_upper]
  have hi : (1 / (542152719267871 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1211 / 800 : ℝ) - (121 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (542152719267871 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (542152719267871 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((121 / 320 : ℝ) - Real.pi * Real.exp (1211 / 800 : ℝ)) := by
    rw [show (121 / 320 : ℝ) - Real.pi * Real.exp (1211 / 800 : ℝ) =
      -(Real.pi * Real.exp (1211 / 800 : ℝ) - (121 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (121 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (121 / 80 : ℝ)) := by
    have h := hpThetaJensenCell1210_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (542152719267871 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1210_endpointUpper :
    hpThetaJensenKernelEndpointUpper (121 / 160 : ℝ) (1211 / 1600 : ℝ) ≤ (686819 / 500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1211 / 800 : ℝ)) (71372875955780581 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1211 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1210_product_upper
  have hD : (10648037633652763 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (121 / 80 : ℝ) - (1211 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1210_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1210_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (121 / 80 : ℝ) - (1211 / 3200 : ℝ)) ≤
      (1 / (10648037633652763 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (10648037633652763 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1211 / 3200 : ℝ) - Real.pi * Real.exp (121 / 80 : ℝ)) ≤
      (2 / (10648037633652763 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1211 / 3200 : ℝ) - Real.pi * Real.exp (121 / 80 : ℝ) =
      -(Real.pi * Real.exp (121 / 80 : ℝ) - (1211 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (71372875955780581 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (71372875955780581 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1210_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (121 / 160 : ℝ) (1211 / 1600 : ℝ)) :
    (13418321 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (686819 / 500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1210_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1210_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1211_leftExp :
    (45437379031 / 10000000000 : ℝ) ≤ Real.exp (1211 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1211 / 800 : ℝ) (104844140741 / 100000000000 : ℝ)
    (45437379031 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1211_rightExp :
    Real.exp (303 / 200 : ℝ) ≤ (4549421127 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (303 / 200 : ℝ) (1048482362953 / 1000000000000 : ℝ)
    (4549421127 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1211_denomUpper :
    Real.exp (13913992066635311 / 1000000000000000 : ℝ) ≤ (11034939991376169 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (13913992066635311 / 1000000000000000 : ℝ) (772336511291
    / 500000000000 : ℝ) (11034939991376169 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1211_denomLower :
    (1354528793287067 / 1250000000 : ℝ) ≤ Real.exp (17369775808094669 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (17369775808094669 / 1250000000000000 : ℝ) (77189805919 /
    50000000000 : ℝ) (1354528793287067 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1211_product_lower :
    (17843213308094669 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1211 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1211_leftExp
    (by norm_num : (0 : ℝ) ≤ (45437379031 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1211_product_upper :
    Real.pi * Real.exp (303 / 200 : ℝ) ≤ (14292429566635311 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1211_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1211_endpointLower :
    (413123 / 312500000 : ℝ) ≤ hpThetaTraceEndpointLower (1211 / 1600 : ℝ) (303 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (17843213308094669 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1211 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1211_product_lower
  have hD : Real.exp (Real.pi * Real.exp (303 / 200 : ℝ) - (1211 / 3200 : ℝ)) ≤
      (11034939991376169 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1211_denomUpper
    linarith [hpThetaJensenCell1211_product_upper]
  have hi : (1 / (11034939991376169 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (303 / 200 : ℝ) - (1211 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (11034939991376169 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (11034939991376169 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1211 / 3200 : ℝ) - Real.pi * Real.exp (303 / 200 : ℝ)) := by
    rw [show (1211 / 3200 : ℝ) - Real.pi * Real.exp (303 / 200 : ℝ) =
      -(Real.pi * Real.exp (303 / 200 : ℝ) - (1211 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1211 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1211 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1211_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (11034939991376169 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1211_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1211 / 1600 : ℝ) (303 / 400 : ℝ) ≤ (1691699 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (303 / 200 : ℝ)) (14292429566635311 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (303 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1211_product_upper
  have hD : (1354528793287067 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1211 / 800 : ℝ) - (303 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1211_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1211_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1211 / 800 : ℝ) - (303 / 800 : ℝ)) ≤
      (1 / (1354528793287067 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1354528793287067 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((303 / 800 : ℝ) - Real.pi * Real.exp (1211 / 800 : ℝ)) ≤
      (2 / (1354528793287067 / 1250000000 : ℝ) : ℝ) := by
    rw [show (303 / 800 : ℝ) - Real.pi * Real.exp (1211 / 800 : ℝ) =
      -(Real.pi * Real.exp (1211 / 800 : ℝ) - (303 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (14292429566635311 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (14292429566635311 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1211_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1211 / 1600 : ℝ) (303 / 400 : ℝ)) :
    (413123 / 312500000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1691699 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1211_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1211_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1212_leftExp :
    (45494211267 / 10000000000 : ℝ) ≤ Real.exp (303 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (303 / 200 : ℝ) (131060295369 / 125000000000 : ℝ)
    (45494211267 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1212_rightExp :
    Real.exp (1213 / 800 : ℝ) ≤ (4555111459 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1213 / 800 : ℝ) (209704664019 / 200000000000 : ℝ)
    (4555111459 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1212_denomUpper :
    Real.exp (13931556273814187 / 1000000000000000 : ℝ) ≤ (5615236060090601 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (13931556273814187 / 1000000000000000 : ℝ) (1545521097713
    / 1000000000000 : ℝ) (5615236060090601 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1212_denomLower :
    (1102799512714511 / 1000000000 : ℝ) ≤ Real.exp (17391703145339633 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (17391703145339633 / 1250000000000000 : ℝ) (308928526767
    / 200000000000 : ℝ) (1102799512714511 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1212_product_lower :
    (17865531270339633 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (303 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1212_leftExp
    (by norm_num : (0 : ℝ) ≤ (45494211267 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1212_product_upper :
    Real.pi * Real.exp (1213 / 800 : ℝ) ≤ (14310306273814187 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1212_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1212_endpointLower :
    (13024191 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (303 / 400 : ℝ) (1213 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (17865531270339633 / 1250000000000000 : ℝ) (Real.pi * Real.exp (303 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1212_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1213 / 800 : ℝ) - (303 / 800 : ℝ)) ≤
      (5615236060090601 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1212_denomUpper
    linarith [hpThetaJensenCell1212_product_upper]
  have hi : (1 / (5615236060090601 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1213 / 800 : ℝ) - (303 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5615236060090601 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5615236060090601 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((303 / 800 : ℝ) - Real.pi * Real.exp (1213 / 800 : ℝ)) := by
    rw [show (303 / 800 : ℝ) - Real.pi * Real.exp (1213 / 800 : ℝ) =
      -(Real.pi * Real.exp (1213 / 800 : ℝ) - (303 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (303 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (303 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1212_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5615236060090601 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1212_endpointUpper :
    hpThetaJensenKernelEndpointUpper (303 / 400 : ℝ) (1213 / 1600 : ℝ) ≤ (6666749 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1213 / 800 : ℝ)) (14310306273814187 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1213 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1212_product_upper
  have hD : (1102799512714511 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (303 / 200 : ℝ) - (1213 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1212_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1212_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (303 / 200 : ℝ) - (1213 / 3200 : ℝ)) ≤
      (1 / (1102799512714511 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1102799512714511 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1213 / 3200 : ℝ) - Real.pi * Real.exp (303 / 200 : ℝ)) ≤
      (2 / (1102799512714511 / 1000000000 : ℝ) : ℝ) := by
    rw [show (1213 / 3200 : ℝ) - Real.pi * Real.exp (303 / 200 : ℝ) =
      -(Real.pi * Real.exp (303 / 200 : ℝ) - (1213 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (14310306273814187 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (14310306273814187 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1212_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (303 / 400 : ℝ) (1213 / 1600 : ℝ)) :
    (13024191 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6666749 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1212_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1212_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1213_leftExp :
    (11387778647 / 2500000000 : ℝ) ≤ Real.exp (1213 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1213 / 800 : ℝ) (524261660047 / 500000000000 : ℝ)
    (11387778647 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1213_rightExp :
    Real.exp (607 / 400 : ℝ) ≤ (9121617817 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (607 / 400 : ℝ) (1048564278837 / 1000000000000 : ℝ)
    (9121617817 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1213_denomUpper :
    Real.exp (27898285682562481 / 2000000000000000 : ℝ) ≤ (1428715565413491 / 1250000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (27898285682562481 / 2000000000000000 : ℝ) (309274143801
    / 200000000000 : ℝ) (1428715565413491 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1213_denomLower :
    (175365689641233 / 156250000 : ℝ) ≤ Real.exp (4353414599398253 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4353414599398253 / 312500000000000 : ℝ) (772745346011 /
    500000000000 : ℝ) (175365689641233 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1213_product_lower :
    (4471969286898253 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (1213 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1213_leftExp
    (by norm_num : (0 : ℝ) ≤ (11387778647 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1213_product_upper :
    Real.pi * Real.exp (607 / 400 : ℝ) ≤ (28656410682562481 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1213_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1213_endpointLower :
    (2566211 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1213 / 1600 : ℝ) (607 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4471969286898253 / 312500000000000 : ℝ) (Real.pi * Real.exp (1213 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1213_product_lower
  have hD : Real.exp (Real.pi * Real.exp (607 / 400 : ℝ) - (1213 / 3200 : ℝ)) ≤
      (1428715565413491 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1213_denomUpper
    linarith [hpThetaJensenCell1213_product_upper]
  have hi : (1 / (1428715565413491 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (607 / 400 : ℝ) - (1213 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1428715565413491 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1428715565413491 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1213 / 3200 : ℝ) - Real.pi * Real.exp (607 / 400 : ℝ)) := by
    rw [show (1213 / 3200 : ℝ) - Real.pi * Real.exp (607 / 400 : ℝ) =
      -(Real.pi * Real.exp (607 / 400 : ℝ) - (1213 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1213 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1213 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1213_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1428715565413491 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1213_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1213 / 1600 : ℝ) (607 / 800 : ℝ) ≤ (6568033 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (607 / 400 : ℝ)) (28656410682562481 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (607 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1213_product_upper
  have hD : (175365689641233 / 156250000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1213 / 800 : ℝ) - (607 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1213_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1213_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1213 / 800 : ℝ) - (607 / 1600 : ℝ)) ≤
      (1 / (175365689641233 / 156250000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (175365689641233 / 156250000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((607 / 1600 : ℝ) - Real.pi * Real.exp (1213 / 800 : ℝ)) ≤
      (2 / (175365689641233 / 156250000 : ℝ) : ℝ) := by
    rw [show (607 / 1600 : ℝ) - Real.pi * Real.exp (1213 / 800 : ℝ) =
      -(Real.pi * Real.exp (1213 / 800 : ℝ) - (607 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (28656410682562481 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (28656410682562481 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1213_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1213 / 1600 : ℝ) (607 / 800 : ℝ)) :
    (2566211 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6568033 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1213_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1213_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1214_leftExp :
    (45608089083 / 10000000000 : ℝ) ≤ Real.exp (607 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (607 / 400 : ℝ) (262141069709 / 250000000000 : ℝ)
    (45608089083 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1214_rightExp :
    Real.exp (243 / 160 : ℝ) ≤ (11416283711 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (243 / 160 : ℝ) (52430261959 / 50000000000 : ℝ)
    (11416283711 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1214_denomUpper :
    Real.exp (34916879492491623 / 2500000000000000 : ℝ) ≤ (5816386260635197 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (34916879492491623 / 2500000000000000 : ℝ) (1547221889847
    / 1000000000000 : ℝ) (5816386260635197 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1214_denomLower :
    (2855632768474649 / 2500000000 : ℝ) ≤ Real.exp (17435641599805017 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (17435641599805017 / 1250000000000000 : ℝ) (1546340296323
    / 1000000000000 : ℝ) (2855632768474649 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1214_product_lower :
    (17910250974805017 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (607 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1214_leftExp
    (by norm_num : (0 : ℝ) ≤ (45608089083 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1214_product_upper :
    Real.pi * Real.exp (243 / 160 : ℝ) ≤ (35865316992491623 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1214_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1214_endpointLower :
    (12640497 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (607 / 800 : ℝ) (243 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (17910250974805017 / 1250000000000000 : ℝ) (Real.pi * Real.exp (607 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1214_product_lower
  have hD : Real.exp (Real.pi * Real.exp (243 / 160 : ℝ) - (607 / 1600 : ℝ)) ≤
      (5816386260635197 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1214_denomUpper
    linarith [hpThetaJensenCell1214_product_upper]
  have hi : (1 / (5816386260635197 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (243 / 160 : ℝ) - (607 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5816386260635197 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5816386260635197 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((607 / 1600 : ℝ) - Real.pi * Real.exp (243 / 160 : ℝ)) := by
    rw [show (607 / 1600 : ℝ) - Real.pi * Real.exp (243 / 160 : ℝ) =
      -(Real.pi * Real.exp (243 / 160 : ℝ) - (607 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (607 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (607 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1214_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5816386260635197 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1214_endpointUpper :
    hpThetaJensenKernelEndpointUpper (607 / 800 : ℝ) (243 / 320 : ℝ) ≤ (6470633 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (243 / 160 : ℝ)) (35865316992491623 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (243 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1214_product_upper
  have hD : (2855632768474649 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (607 / 400 : ℝ) - (243 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1214_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1214_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (607 / 400 : ℝ) - (243 / 640 : ℝ)) ≤
      (1 / (2855632768474649 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2855632768474649 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((243 / 640 : ℝ) - Real.pi * Real.exp (607 / 400 : ℝ)) ≤
      (2 / (2855632768474649 / 2500000000 : ℝ) : ℝ) := by
    rw [show (243 / 640 : ℝ) - Real.pi * Real.exp (607 / 400 : ℝ) =
      -(Real.pi * Real.exp (607 / 400 : ℝ) - (243 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (35865316992491623 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (35865316992491623 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1214_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (607 / 800 : ℝ) (243 / 320 : ℝ)) :
    (12640497 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6470633 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1214_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1214_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1215_leftExp :
    (45665134841 / 10000000000 : ℝ) ≤ Real.exp (243 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (243 / 160 : ℝ) (1048605239179 / 1000000000000 : ℝ)
    (45665134841 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1215_rightExp :
    Real.exp (38 / 25 : ℝ) ≤ (45722251953 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (38 / 25 : ℝ) (524323100561 / 500000000000 : ℝ)
    (45722251953 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1215_denomUpper :
    Real.exp (139843831679781129 / 10000000000000000 : ℝ) ≤ (11839693034902323 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (139843831679781129 / 10000000000000000 : ℝ)
    (154807461359 / 100000000000 : ℝ) (11839693034902323 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1215_denomLower :
    (11625451210831743 / 10000000000 : ℝ) ≤ Real.exp (17457652786925859 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (17457652786925859 / 1250000000000000 : ℝ) (96699465633 /
    62500000000 : ℝ) (11625451210831743 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1215_product_lower :
    (17932652786925859 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (243 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1215_leftExp
    (by norm_num : (0 : ℝ) ≤ (45665134841 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1215_product_upper :
    Real.pi * Real.exp (38 / 25 : ℝ) ≤ (143640706679781129 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1215_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1215_endpointLower :
    (12452487 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (243 / 320 : ℝ) (19 / 25 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (17932652786925859 / 1250000000000000 : ℝ) (Real.pi * Real.exp (243 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1215_product_lower
  have hD : Real.exp (Real.pi * Real.exp (38 / 25 : ℝ) - (243 / 640 : ℝ)) ≤
      (11839693034902323 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1215_denomUpper
    linarith [hpThetaJensenCell1215_product_upper]
  have hi : (1 / (11839693034902323 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (38 / 25 : ℝ) - (243 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (11839693034902323 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (11839693034902323 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((243 / 640 : ℝ) - Real.pi * Real.exp (38 / 25 : ℝ)) := by
    rw [show (243 / 640 : ℝ) - Real.pi * Real.exp (38 / 25 : ℝ) =
      -(Real.pi * Real.exp (38 / 25 : ℝ) - (243 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (243 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (243 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1215_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (11839693034902323 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1215_endpointUpper :
    hpThetaJensenKernelEndpointUpper (243 / 320 : ℝ) (19 / 25 : ℝ) ≤ (6374533 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (38 / 25 : ℝ)) (143640706679781129 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (19 / 25 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1215_product_upper
  have hD : (11625451210831743 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (243 / 160 : ℝ) - (19 / 50 : ℝ)) := by
    apply le_trans hpThetaJensenCell1215_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1215_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (243 / 160 : ℝ) - (19 / 50 : ℝ)) ≤
      (1 / (11625451210831743 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (11625451210831743 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((19 / 50 : ℝ) - Real.pi * Real.exp (243 / 160 : ℝ)) ≤
      (2 / (11625451210831743 / 10000000000 : ℝ) : ℝ) := by
    rw [show (19 / 50 : ℝ) - Real.pi * Real.exp (243 / 160 : ℝ) =
      -(Real.pi * Real.exp (243 / 160 : ℝ) - (19 / 50 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (143640706679781129 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (143640706679781129 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1215_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (243 / 320 : ℝ) (19 / 25 : ℝ)) :
    (12452487 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6374533 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1215_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1215_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1216_leftExp :
    (45722251951 / 10000000000 : ℝ) ≤ Real.exp (38 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (38 / 25 : ℝ) (1048646201121 / 1000000000000 : ℝ)
    (45722251951 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1216_rightExp :
    Real.exp (1217 / 800 : ℝ) ≤ (45779440503 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1217 / 800 : ℝ) (131085895583 / 125000000000 : ℝ)
    (45779440503 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1216_denomUpper :
    Real.exp (140020369828141279 / 10000000000000000 : ℝ) ≤ (12050564651246937 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (140020369828141279 / 10000000000000000 : ℝ)
    (154892889367 / 100000000000 : ℝ) (12050564651246937 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1216_denomLower :
    (2958060357818339 / 2500000000 : ℝ) ≤ Real.exp (17479691993905749 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (17479691993905749 / 1250000000000000 : ℝ) (774022078417
    / 500000000000 : ℝ) (2958060357818339 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1216_product_lower :
    (17955082618905749 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (38 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1216_leftExp
    (by norm_num : (0 : ℝ) ≤ (45722251951 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1216_product_upper :
    Real.pi * Real.exp (1217 / 800 : ℝ) ≤ (143820369828141279 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1216_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1216_endpointLower :
    (3066749 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (19 / 25 : ℝ) (1217 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (17955082618905749 / 1250000000000000 : ℝ) (Real.pi * Real.exp (38 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell1216_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1217 / 800 : ℝ) - (19 / 50 : ℝ)) ≤
      (12050564651246937 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1216_denomUpper
    linarith [hpThetaJensenCell1216_product_upper]
  have hi : (1 / (12050564651246937 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1217 / 800 : ℝ) - (19 / 50 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (12050564651246937 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (12050564651246937 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((19 / 50 : ℝ) - Real.pi * Real.exp (1217 / 800 : ℝ)) := by
    rw [show (19 / 50 : ℝ) - Real.pi * Real.exp (1217 / 800 : ℝ) =
      -(Real.pi * Real.exp (1217 / 800 : ℝ) - (19 / 50 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (38 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (38 / 25 : ℝ)) := by
    have h := hpThetaJensenCell1216_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (12050564651246937 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1216_endpointUpper :
    hpThetaJensenKernelEndpointUpper (19 / 25 : ℝ) (1217 / 1600 : ℝ) ≤ (3139859 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1217 / 800 : ℝ)) (143820369828141279 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1217 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1216_product_upper
  have hD : (2958060357818339 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (38 / 25 : ℝ) - (1217 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1216_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1216_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (38 / 25 : ℝ) - (1217 / 3200 : ℝ)) ≤
      (1 / (2958060357818339 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2958060357818339 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1217 / 3200 : ℝ) - Real.pi * Real.exp (38 / 25 : ℝ)) ≤
      (2 / (2958060357818339 / 2500000000 : ℝ) : ℝ) := by
    rw [show (1217 / 3200 : ℝ) - Real.pi * Real.exp (38 / 25 : ℝ) =
      -(Real.pi * Real.exp (38 / 25 : ℝ) - (1217 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (143820369828141279 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (143820369828141279 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1216_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (19 / 25 : ℝ) (1217 / 1600 : ℝ)) :
    (3066749 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3139859 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1216_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1216_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1217_leftExp :
    (91558881 / 20000000 : ℝ) ≤ Real.exp (1217 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1217 / 800 : ℝ) (1048687164663 / 1000000000000 : ℝ)
    (91558881 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1217_rightExp :
    Real.exp (609 / 400 : ℝ) ≤ (5729587573 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (609 / 400 : ℝ) (1048728129807 / 1000000000000 : ℝ)
    (5729587573 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1217_denomUpper :
    Real.exp (17524641587223789 / 1250000000000000 : ℝ) ≤ (613273381897753 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (17524641587223789 / 1250000000000000 : ℝ) (193723091689
    / 125000000000 : ℝ) (613273381897753 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1217_denomLower :
    (602149012873423 / 500000000 : ℝ) ≤ Real.exp (35003518509819 / 2500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (35003518509819 / 2500000000000 : ℝ) (774449209907 /
    500000000000 : ℝ) (602149012873423 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1217_product_lower :
    (35955081009819 / 2500000000000 : ℝ) ≤ Real.pi * Real.exp (1217 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1217_leftExp
    (by norm_num : (0 : ℝ) ≤ (91558881 / 20000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1217_product_upper :
    Real.pi * Real.exp (609 / 400 : ℝ) ≤ (18000032212223789 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1217_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1217_endpointLower :
    (6041997 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1217 / 1600 : ℝ) (609 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (35955081009819 / 2500000000000 : ℝ) (Real.pi * Real.exp (1217 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1217_product_lower
  have hD : Real.exp (Real.pi * Real.exp (609 / 400 : ℝ) - (1217 / 3200 : ℝ)) ≤
      (613273381897753 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1217_denomUpper
    linarith [hpThetaJensenCell1217_product_upper]
  have hi : (1 / (613273381897753 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (609 / 400 : ℝ) - (1217 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (613273381897753 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (613273381897753 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1217 / 3200 : ℝ) - Real.pi * Real.exp (609 / 400 : ℝ)) := by
    rw [show (1217 / 3200 : ℝ) - Real.pi * Real.exp (609 / 400 : ℝ) =
      -(Real.pi * Real.exp (609 / 400 : ℝ) - (1217 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1217 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1217 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1217_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (613273381897753 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1217_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1217 / 1600 : ℝ) (609 / 800 : ℝ) ≤ (12372347 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (609 / 400 : ℝ)) (18000032212223789 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (609 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1217_product_upper
  have hD : (602149012873423 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1217 / 800 : ℝ) - (609 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1217_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1217_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1217 / 800 : ℝ) - (609 / 1600 : ℝ)) ≤
      (1 / (602149012873423 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (602149012873423 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((609 / 1600 : ℝ) - Real.pi * Real.exp (1217 / 800 : ℝ)) ≤
      (2 / (602149012873423 / 500000000 : ℝ) : ℝ) := by
    rw [show (609 / 1600 : ℝ) - Real.pi * Real.exp (1217 / 800 : ℝ) =
      -(Real.pi * Real.exp (1217 / 800 : ℝ) - (609 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (18000032212223789 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (18000032212223789 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1217_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1217 / 1600 : ℝ) (609 / 800 : ℝ)) :
    (6041997 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (12372347 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1217_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1217_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1218_leftExp :
    (22918350291 / 5000000000 : ℝ) ≤ Real.exp (609 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (609 / 400 : ℝ) (524364064903 / 500000000000 : ℝ)
    (22918350291 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1218_rightExp :
    Real.exp (1219 / 800 : ℝ) ≤ (11473508071 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1219 / 800 : ℝ) (1048769096549 / 1000000000000 : ℝ)
    (11473508071 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1218_denomUpper :
    Real.exp (35093530141297103 / 2500000000000000 : ℝ) ≤ (12484483978539163 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (35093530141297103 / 2500000000000000 : ℝ) (1550642136521
    / 1000000000000 : ℝ) (12484483978539163 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1218_denomLower :
    (490309916881351 / 400000000 : ℝ) ≤ Real.exp (8761927303425409 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8761927303425409 / 625000000000000 : ℝ) (387438560639 /
    250000000000 : ℝ) (490309916881351 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1218_product_lower :
    (9000013240925409 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (609 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1218_leftExp
    (by norm_num : (0 : ℝ) ≤ (22918350291 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1218_product_upper :
    Real.pi * Real.exp (1219 / 800 : ℝ) ≤ (36045092641297103 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1218_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1218_endpointLower :
    (2975863 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (609 / 800 : ℝ) (1219 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9000013240925409 / 625000000000000 : ℝ) (Real.pi * Real.exp (609 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1218_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1219 / 800 : ℝ) - (609 / 1600 : ℝ)) ≤
      (12484483978539163 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1218_denomUpper
    linarith [hpThetaJensenCell1218_product_upper]
  have hi : (1 / (12484483978539163 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1219 / 800 : ℝ) - (609 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (12484483978539163 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (12484483978539163 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((609 / 1600 : ℝ) - Real.pi * Real.exp (1219 / 800 : ℝ)) := by
    rw [show (609 / 1600 : ℝ) - Real.pi * Real.exp (1219 / 800 : ℝ) =
      -(Real.pi * Real.exp (1219 / 800 : ℝ) - (609 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (609 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (609 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1218_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (12484483978539163 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1218_endpointUpper :
    hpThetaJensenKernelEndpointUpper (609 / 800 : ℝ) (1219 / 1600 : ℝ) ≤ (12187769 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1219 / 800 : ℝ)) (36045092641297103 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1219 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1218_product_upper
  have hD : (490309916881351 / 400000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (609 / 400 : ℝ) - (1219 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1218_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1218_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (609 / 400 : ℝ) - (1219 / 3200 : ℝ)) ≤
      (1 / (490309916881351 / 400000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (490309916881351 / 400000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1219 / 3200 : ℝ) - Real.pi * Real.exp (609 / 400 : ℝ)) ≤
      (2 / (490309916881351 / 400000000 : ℝ) : ℝ) := by
    rw [show (1219 / 3200 : ℝ) - Real.pi * Real.exp (609 / 400 : ℝ) =
      -(Real.pi * Real.exp (609 / 400 : ℝ) - (1219 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (36045092641297103 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (36045092641297103 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1218_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (609 / 800 : ℝ) (1219 / 1600 : ℝ)) :
    (2975863 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (12187769 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1218_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1218_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1219_leftExp :
    (22947016141 / 5000000000 : ℝ) ≤ Real.exp (1219 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1219 / 800 : ℝ) (262192274137 / 250000000000 : ℝ)
    (22947016141 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1219_rightExp :
    Real.exp (61 / 40 : ℝ) ≤ (22975717847 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (61 / 40 : ℝ) (262202516223 / 250000000000 : ℝ)
    (22975717847 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1219_denomUpper :
    Real.exp (70275666858110271 / 5000000000000000 : ℝ) ≤ (254153948589781 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (70275666858110271 / 5000000000000000 : ℝ) (775750553077
    / 500000000000 : ℝ) (254153948589781 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1219_denomLower :
    (1247662634538937 / 1000000000 : ℝ) ≤ Real.exp (8772989041554559 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8772989041554559 / 625000000000000 : ℝ) (1550611628419 /
    1000000000000 : ℝ) (1247662634538937 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1219_product_lower :
    (9011270291554559 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1219 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1219_leftExp
    (by norm_num : (0 : ℝ) ≤ (22947016141 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1219_product_upper :
    Real.pi * Real.exp (61 / 40 : ℝ) ≤ (72180354358110271 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1219_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1219_endpointLower :
    (11725341 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1219 / 1600 : ℝ) (61 / 80 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9011270291554559 / 625000000000000 : ℝ) (Real.pi * Real.exp (1219 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1219_product_lower
  have hD : Real.exp (Real.pi * Real.exp (61 / 40 : ℝ) - (1219 / 3200 : ℝ)) ≤
      (254153948589781 / 200000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1219_denomUpper
    linarith [hpThetaJensenCell1219_product_upper]
  have hi : (1 / (254153948589781 / 200000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (61 / 40 : ℝ) - (1219 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (254153948589781 / 200000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (254153948589781 / 200000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1219 / 3200 : ℝ) - Real.pi * Real.exp (61 / 40 : ℝ)) := by
    rw [show (1219 / 3200 : ℝ) - Real.pi * Real.exp (61 / 40 : ℝ) =
      -(Real.pi * Real.exp (61 / 40 : ℝ) - (1219 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1219 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1219 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1219_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (254153948589781 / 200000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1219_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1219 / 1600 : ℝ) (61 / 80 : ℝ) ≤ (12005671 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (61 / 40 : ℝ)) (72180354358110271 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (61 / 80 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1219_product_upper
  have hD : (1247662634538937 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1219 / 800 : ℝ) - (61 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell1219_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1219_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1219 / 800 : ℝ) - (61 / 160 : ℝ)) ≤
      (1 / (1247662634538937 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1247662634538937 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((61 / 160 : ℝ) - Real.pi * Real.exp (1219 / 800 : ℝ)) ≤
      (2 / (1247662634538937 / 1000000000 : ℝ) : ℝ) := by
    rw [show (61 / 160 : ℝ) - Real.pi * Real.exp (1219 / 800 : ℝ) =
      -(Real.pi * Real.exp (1219 / 800 : ℝ) - (61 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (72180354358110271 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (72180354358110271 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1219_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1219 / 1600 : ℝ) (61 / 80 : ℝ)) :
    (11725341 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (12005671 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1219_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1219_endpointUpper

def hpThetaJensenCellsBatch060Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (7777153 / 5000000000 : ℝ)
  | 1 => (3831943 / 2500000000 : ℝ)
  | 2 => (7552101 / 5000000000 : ℝ)
  | 3 => (372089 / 250000000 : ℝ)
  | 4 => (2933163 / 2000000000 : ℝ)
  | 5 => (3612733 / 2500000000 : ℝ)
  | 6 => (14238879 / 10000000000 : ℝ)
  | 7 => (1753703 / 1250000000 : ℝ)
  | 8 => (13823133 / 10000000000 : ℝ)
  | 9 => (851211 / 625000000 : ℝ)
  | 10 => (13418321 / 10000000000 : ℝ)
  | 11 => (413123 / 312500000 : ℝ)
  | 12 => (13024191 / 10000000000 : ℝ)
  | 13 => (2566211 / 2000000000 : ℝ)
  | 14 => (12640497 / 10000000000 : ℝ)
  | 15 => (12452487 / 10000000000 : ℝ)
  | 16 => (3066749 / 2500000000 : ℝ)
  | 17 => (6041997 / 5000000000 : ℝ)
  | 18 => (2975863 / 2500000000 : ℝ)
  | 19 => (11725341 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch060Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (31839 / 20000000 : ℝ)
  | 1 => (15687991 / 10000000000 : ℝ)
  | 2 => (966219 / 625000000 : ℝ)
  | 3 => (3046801 / 2000000000 : ℝ)
  | 4 => (7505731 / 5000000000 : ℝ)
  | 5 => (14791839 / 10000000000 : ℝ)
  | 6 => (28467 / 19531250 : ℝ)
  | 7 => (14361223 / 10000000000 : ℝ)
  | 8 => (3537541 / 2500000000 : ℝ)
  | 9 => (13941893 / 10000000000 : ℝ)
  | 10 => (686819 / 500000000 : ℝ)
  | 11 => (1691699 / 1250000000 : ℝ)
  | 12 => (6666749 / 5000000000 : ℝ)
  | 13 => (6568033 / 5000000000 : ℝ)
  | 14 => (6470633 / 5000000000 : ℝ)
  | 15 => (6374533 / 5000000000 : ℝ)
  | 16 => (3139859 / 2500000000 : ℝ)
  | 17 => (12372347 / 10000000000 : ℝ)
  | 18 => (12187769 / 10000000000 : ℝ)
  | 19 => (12005671 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch060_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1200 : ℝ) + (j.val : ℝ)) / 1600)
      (((1200 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch060Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch060Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1200_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1201_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1202_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1203_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1204_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1205_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1206_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1207_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1208_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1209_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1210_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1211_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1212_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1213_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1214_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1215_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1216_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1217_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1218_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1219_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper] at h ⊢
    exact h

end HodgeProofHP
