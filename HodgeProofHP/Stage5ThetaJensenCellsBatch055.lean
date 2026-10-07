import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1100_leftExp :
    (39550767229 / 10000000000 : ℝ) ≤ Real.exp (11 / 8 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11 / 8 : ℝ) (1043905272301 / 1000000000000 : ℝ)
    (39550767229 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1100_rightExp :
    Real.exp (1101 / 800 : ℝ) ≤ (19800118301 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1101 / 800 : ℝ) (130493256331 / 125000000000 : ℝ)
    (19800118301 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1100_denomUpper :
    Real.exp (60485163053593493 / 5000000000000000 : ℝ) ≤ (179338903559059 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (60485163053593493 / 5000000000000000 : ℝ) (1459410035943
    / 1000000000000 : ℝ) (179338903559059 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1100_denomLower :
    (1765174278845239 / 10000000000 : ℝ) ≤ Real.exp (15101468615061071 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (15101468615061071 / 1250000000000000 : ℝ) (1458686999053
    / 1000000000000 : ℝ) (1765174278845239 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1100_product_lower :
    (15531546740061071 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (11 / 8 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1100_leftExp
    (by norm_num : (0 : ℝ) ≤ (39550767229 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1100_product_upper :
    Real.pi * Real.exp (1101 / 800 : ℝ) ≤ (62203913053593493 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1100_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1100_endpointLower :
    (12111029 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (11 / 16 : ℝ) (1101 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (15531546740061071 / 1250000000000000 : ℝ) (Real.pi * Real.exp (11 / 8 : ℝ))
    (by norm_num) hpThetaJensenCell1100_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1101 / 800 : ℝ) - (11 / 32 : ℝ)) ≤
      (179338903559059 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1100_denomUpper
    linarith [hpThetaJensenCell1100_product_upper]
  have hi : (1 / (179338903559059 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1101 / 800 : ℝ) - (11 / 32 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (179338903559059 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (179338903559059 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((11 / 32 : ℝ) - Real.pi * Real.exp (1101 / 800 : ℝ)) := by
    rw [show (11 / 32 : ℝ) - Real.pi * Real.exp (1101 / 800 : ℝ) =
      -(Real.pi * Real.exp (1101 / 800 : ℝ) - (11 / 32 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (11 / 8 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (11 / 8 : ℝ)) := by
    have h := hpThetaJensenCell1100_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (179338903559059 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1100_endpointUpper :
    hpThetaJensenKernelEndpointUpper (11 / 16 : ℝ) (1101 / 1600 : ℝ) ≤ (1932817 / 312500000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1101 / 800 : ℝ)) (62203913053593493 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1101 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1100_product_upper
  have hD : (1765174278845239 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (11 / 8 : ℝ) - (1101 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1100_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1100_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (11 / 8 : ℝ) - (1101 / 3200 : ℝ)) ≤
      (1 / (1765174278845239 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1765174278845239 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1101 / 3200 : ℝ) - Real.pi * Real.exp (11 / 8 : ℝ)) ≤
      (2 / (1765174278845239 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1101 / 3200 : ℝ) - Real.pi * Real.exp (11 / 8 : ℝ) =
      -(Real.pi * Real.exp (11 / 8 : ℝ) - (1101 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (62203913053593493 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (62203913053593493 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1100_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (11 / 16 : ℝ) (1101 / 1600 : ℝ)) :
    (12111029 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1932817 / 312500000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1100_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1100_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1101_leftExp :
    (39600236599 / 10000000000 : ℝ) ≤ Real.exp (1101 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1101 / 800 : ℝ) (1043946050647 / 1000000000000 : ℝ)
    (39600236599 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1101_rightExp :
    Real.exp (551 / 400 : ℝ) ≤ (4956220981 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (551 / 400 : ℝ) (1043986830587 / 1000000000000 : ℝ)
    (4956220981 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1101_denomUpper :
    Real.exp (15140351015362733 / 1250000000000000 : ℝ) ≤ (910472272590567 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (15140351015362733 / 1250000000000000 : ℝ) (146010561973
    / 100000000000 : ℝ) (910472272590567 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1101_denomLower :
    (1792261418478767 / 10000000000 : ℝ) ≤ Real.exp (15120504562190701 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (15120504562190701 / 1250000000000000 : ℝ) (58375254059 /
    40000000000 : ℝ) (1792261418478767 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1101_product_lower :
    (15550973312190701 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1101 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1101_leftExp
    (by norm_num : (0 : ℝ) ≤ (39600236599 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1101_product_upper :
    Real.pi * Real.exp (551 / 400 : ℝ) ≤ (15570429140362733 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1101_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1101_endpointLower :
    (5979833 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1101 / 1600 : ℝ) (551 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (15550973312190701 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1101 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1101_product_lower
  have hD : Real.exp (Real.pi * Real.exp (551 / 400 : ℝ) - (1101 / 3200 : ℝ)) ≤
      (910472272590567 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1101_denomUpper
    linarith [hpThetaJensenCell1101_product_upper]
  have hi : (1 / (910472272590567 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (551 / 400 : ℝ) - (1101 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (910472272590567 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (910472272590567 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1101 / 3200 : ℝ) - Real.pi * Real.exp (551 / 400 : ℝ)) := by
    rw [show (1101 / 3200 : ℝ) - Real.pi * Real.exp (551 / 400 : ℝ) =
      -(Real.pi * Real.exp (551 / 400 : ℝ) - (1101 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1101 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1101 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1101_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (910472272590567 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1101_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1101 / 1600 : ℝ) (551 / 800 : ℝ) ≤ (61078317 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (551 / 400 : ℝ)) (15570429140362733 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (551 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1101_product_upper
  have hD : (1792261418478767 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1101 / 800 : ℝ) - (551 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1101_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1101_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1101 / 800 : ℝ) - (551 / 1600 : ℝ)) ≤
      (1 / (1792261418478767 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1792261418478767 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((551 / 1600 : ℝ) - Real.pi * Real.exp (1101 / 800 : ℝ)) ≤
      (2 / (1792261418478767 / 10000000000 : ℝ) : ℝ) := by
    rw [show (551 / 1600 : ℝ) - Real.pi * Real.exp (1101 / 800 : ℝ) =
      -(Real.pi * Real.exp (1101 / 800 : ℝ) - (551 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (15570429140362733 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (15570429140362733 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1101_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1101 / 1600 : ℝ) (551 / 800 : ℝ)) :
    (5979833 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (61078317 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1101_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1101_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1102_leftExp :
    (19824883923 / 5000000000 : ℝ) ≤ Real.exp (551 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (551 / 400 : ℝ) (521993415293 / 500000000000 : ℝ)
    (19824883923 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1102_rightExp :
    Real.exp (1103 / 800 : ℝ) ≤ (39699361047 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1103 / 800 : ℝ) (1044027612119 / 1000000000000 : ℝ)
    (39699361047 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1102_denomUpper :
    Real.exp (121275484769727871 / 10000000000000000 : ℝ) ≤ (1848959432656193 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (121275484769727871 / 10000000000000000 : ℝ)
    (730401211769 / 500000000000 : ℝ) (1848959432656193 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1102_denomLower :
    (1819799593745659 / 10000000000 : ℝ) ≤ Real.exp (7569782404178177 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7569782404178177 / 625000000000000 : ℝ) (1460076921379 /
    1000000000000 : ℝ) (1819799593745659 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1102_product_lower :
    (7785212091678177 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (551 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1102_leftExp
    (by norm_num : (0 : ℝ) ≤ (19824883923 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1102_product_upper :
    Real.pi * Real.exp (1103 / 800 : ℝ) ≤ (124719234769727871 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1102_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1102_endpointLower :
    (5904981 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (551 / 800 : ℝ) (1103 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7785212091678177 / 625000000000000 : ℝ) (Real.pi * Real.exp (551 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1102_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1103 / 800 : ℝ) - (551 / 1600 : ℝ)) ≤
      (1848959432656193 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1102_denomUpper
    linarith [hpThetaJensenCell1102_product_upper]
  have hi : (1 / (1848959432656193 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1103 / 800 : ℝ) - (551 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1848959432656193 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1848959432656193 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((551 / 1600 : ℝ) - Real.pi * Real.exp (1103 / 800 : ℝ)) := by
    rw [show (551 / 1600 : ℝ) - Real.pi * Real.exp (1103 / 800 : ℝ) =
      -(Real.pi * Real.exp (1103 / 800 : ℝ) - (551 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (551 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (551 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1102_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1848959432656193 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1102_endpointUpper :
    hpThetaJensenKernelEndpointUpper (551 / 800 : ℝ) (1103 / 1600 : ℝ) ≤ (30157467 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1103 / 800 : ℝ)) (124719234769727871 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1103 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1102_product_upper
  have hD : (1819799593745659 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (551 / 400 : ℝ) - (1103 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1102_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1102_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (551 / 400 : ℝ) - (1103 / 3200 : ℝ)) ≤
      (1 / (1819799593745659 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1819799593745659 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1103 / 3200 : ℝ) - Real.pi * Real.exp (551 / 400 : ℝ)) ≤
      (2 / (1819799593745659 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1103 / 3200 : ℝ) - Real.pi * Real.exp (551 / 400 : ℝ) =
      -(Real.pi * Real.exp (551 / 400 : ℝ) - (1103 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (124719234769727871 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (124719234769727871 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1102_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (551 / 800 : ℝ) (1103 / 1600 : ℝ)) :
    (5904981 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (30157467 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1102_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1102_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1103_leftExp :
    (7939872209 / 2000000000 : ℝ) ≤ Real.exp (1103 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1103 / 800 : ℝ) (522013806059 / 500000000000 : ℝ)
    (7939872209 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1103_rightExp :
    Real.exp (69 / 50 : ℝ) ≤ (9937254069 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (69 / 50 : ℝ) (261017098811 / 250000000000 : ℝ)
    (9937254069 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1103_denomUpper :
    Real.exp (30357089072391917 / 2500000000000000 : ℝ) ≤ (938720954895811 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (30357089072391917 / 2500000000000000 : ℝ) (730750224951
    / 500000000000 : ℝ) (938720954895811 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1103_denomLower :
    (461949214299461 / 2500000000 : ℝ) ≤ Real.exp (3031729876602091 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3031729876602091 / 250000000000000 : ℝ) (292154742253 /
    200000000000 : ℝ) (461949214299461 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1103_product_lower :
    (3117979876602091 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1103 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1103_leftExp
    (by norm_num : (0 : ℝ) ≤ (7939872209 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1103_product_upper :
    Real.pi * Real.exp (69 / 50 : ℝ) ≤ (31218807822391917 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1103_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1103_endpointLower :
    (58309509 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1103 / 1600 : ℝ) (69 / 100 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3117979876602091 / 250000000000000 : ℝ) (Real.pi * Real.exp (1103 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1103_product_lower
  have hD : Real.exp (Real.pi * Real.exp (69 / 50 : ℝ) - (1103 / 3200 : ℝ)) ≤
      (938720954895811 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1103_denomUpper
    linarith [hpThetaJensenCell1103_product_upper]
  have hi : (1 / (938720954895811 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (69 / 50 : ℝ) - (1103 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (938720954895811 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (938720954895811 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1103 / 3200 : ℝ) - Real.pi * Real.exp (69 / 50 : ℝ)) := by
    rw [show (1103 / 3200 : ℝ) - Real.pi * Real.exp (69 / 50 : ℝ) =
      -(Real.pi * Real.exp (69 / 50 : ℝ) - (1103 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1103 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1103 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1103_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (938720954895811 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1103_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1103 / 1600 : ℝ) (69 / 100 : ℝ) ≤ (59559919 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (69 / 50 : ℝ)) (31218807822391917 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (69 / 100 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1103_product_upper
  have hD : (461949214299461 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1103 / 800 : ℝ) - (69 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1103_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1103_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1103 / 800 : ℝ) - (69 / 200 : ℝ)) ≤
      (1 / (461949214299461 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (461949214299461 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((69 / 200 : ℝ) - Real.pi * Real.exp (1103 / 800 : ℝ)) ≤
      (2 / (461949214299461 / 2500000000 : ℝ) : ℝ) := by
    rw [show (69 / 200 : ℝ) - Real.pi * Real.exp (1103 / 800 : ℝ) =
      -(Real.pi * Real.exp (1103 / 800 : ℝ) - (69 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (31218807822391917 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (31218807822391917 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1103_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1103 / 1600 : ℝ) (69 / 100 : ℝ)) :
    (58309509 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (59559919 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1103_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1103_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1104_leftExp :
    (19874508137 / 5000000000 : ℝ) ≤ Real.exp (69 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (69 / 50 : ℝ) (1044068395243 / 1000000000000 : ℝ)
    (19874508137 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1104_rightExp :
    Real.exp (221 / 160 : ℝ) ≤ (39798733613 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (221 / 160 : ℝ) (522054589981 / 500000000000 : ℝ)
    (39798733613 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1104_denomUpper :
    Real.exp (121581422927465509 / 10000000000000000 : ℝ) ≤ (476600086254747 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (121581422927465509 / 10000000000000000 : ℝ)
    (1462199701377 / 1000000000000 : ℝ) (476600086254747 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1104_denomLower :
    (1876261416032873 / 10000000000 : ℝ) ≤ Real.exp (7588879158391763 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7588879158391763 / 625000000000000 : ℝ) (1461471723683 /
    1000000000000 : ℝ) (1876261416032873 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1104_product_lower :
    (7804699470891763 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (69 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1104_leftExp
    (by norm_num : (0 : ℝ) ≤ (19874508137 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1104_product_upper :
    Real.pi * Real.exp (221 / 160 : ℝ) ≤ (125031422927465509 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1104_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1104_endpointLower :
    (7197169 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (69 / 100 : ℝ) (221 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7804699470891763 / 625000000000000 : ℝ) (Real.pi * Real.exp (69 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell1104_product_lower
  have hD : Real.exp (Real.pi * Real.exp (221 / 160 : ℝ) - (69 / 200 : ℝ)) ≤
      (476600086254747 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1104_denomUpper
    linarith [hpThetaJensenCell1104_product_upper]
  have hi : (1 / (476600086254747 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (221 / 160 : ℝ) - (69 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (476600086254747 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (476600086254747 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((69 / 200 : ℝ) - Real.pi * Real.exp (221 / 160 : ℝ)) := by
    rw [show (69 / 200 : ℝ) - Real.pi * Real.exp (221 / 160 : ℝ) =
      -(Real.pi * Real.exp (221 / 160 : ℝ) - (69 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (69 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (69 / 50 : ℝ)) := by
    have h := hpThetaJensenCell1104_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (476600086254747 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1104_endpointUpper :
    hpThetaJensenKernelEndpointUpper (69 / 100 : ℝ) (221 / 320 : ℝ) ≤ (11762639 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (221 / 160 : ℝ)) (125031422927465509 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (221 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1104_product_upper
  have hD : (1876261416032873 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (69 / 50 : ℝ) - (221 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1104_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1104_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (69 / 50 : ℝ) - (221 / 640 : ℝ)) ≤
      (1 / (1876261416032873 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1876261416032873 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((221 / 640 : ℝ) - Real.pi * Real.exp (69 / 50 : ℝ)) ≤
      (2 / (1876261416032873 / 10000000000 : ℝ) : ℝ) := by
    rw [show (221 / 640 : ℝ) - Real.pi * Real.exp (69 / 50 : ℝ) =
      -(Real.pi * Real.exp (69 / 50 : ℝ) - (221 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (125031422927465509 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (125031422927465509 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1104_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (69 / 100 : ℝ) (221 / 320 : ℝ)) :
    (7197169 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (11762639 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1104_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1104_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1105_leftExp :
    (39798733611 / 10000000000 : ℝ) ≤ Real.exp (221 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (221 / 160 : ℝ) (1044109179961 / 1000000000000 : ℝ)
    (39798733611 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1105_rightExp :
    Real.exp (553 / 400 : ℝ) ≤ (2490532071 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (553 / 400 : ℝ) (522074983137 / 500000000000 : ℝ)
    (2490532071 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1105_denomUpper :
    Real.exp (7608417808029103 / 625000000000000 : ℝ) ≤ (1935843265924479 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7608417808029103 / 625000000000000 : ℝ) (731450090261 /
    500000000000 : ℝ) (1935843265924479 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1105_denomLower :
    (476300408343577 / 2500000000 : ℝ) ≤ Real.exp (15196891640306089 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (15196891640306089 / 1250000000000000 : ℝ) (1462170961187
    / 1000000000000 : ℝ) (476300408343577 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1105_product_lower :
    (15628922890306089 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (221 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1105_leftExp
    (by norm_num : (0 : ℝ) ≤ (39798733611 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1105_product_upper :
    Real.pi * Real.exp (553 / 400 : ℝ) ≤ (7824238120529103 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1105_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1105_endpointLower :
    (56853263 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (221 / 320 : ℝ) (553 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (15628922890306089 / 1250000000000000 : ℝ) (Real.pi * Real.exp (221 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1105_product_lower
  have hD : Real.exp (Real.pi * Real.exp (553 / 400 : ℝ) - (221 / 640 : ℝ)) ≤
      (1935843265924479 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1105_denomUpper
    linarith [hpThetaJensenCell1105_product_upper]
  have hi : (1 / (1935843265924479 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (553 / 400 : ℝ) - (221 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1935843265924479 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1935843265924479 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((221 / 640 : ℝ) - Real.pi * Real.exp (553 / 400 : ℝ)) := by
    rw [show (221 / 640 : ℝ) - Real.pi * Real.exp (553 / 400 : ℝ) =
      -(Real.pi * Real.exp (553 / 400 : ℝ) - (221 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (221 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (221 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1105_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1935843265924479 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1105_endpointUpper :
    hpThetaJensenKernelEndpointUpper (221 / 320 : ℝ) (553 / 800 : ℝ) ≤ (11614937 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (553 / 400 : ℝ)) (7824238120529103 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (553 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1105_product_upper
  have hD : (476300408343577 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (221 / 160 : ℝ) - (553 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1105_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1105_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (221 / 160 : ℝ) - (553 / 1600 : ℝ)) ≤
      (1 / (476300408343577 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (476300408343577 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((553 / 1600 : ℝ) - Real.pi * Real.exp (221 / 160 : ℝ)) ≤
      (2 / (476300408343577 / 2500000000 : ℝ) : ℝ) := by
    rw [show (553 / 1600 : ℝ) - Real.pi * Real.exp (221 / 160 : ℝ) =
      -(Real.pi * Real.exp (221 / 160 : ℝ) - (553 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (7824238120529103 / 625000000000000 : ℝ) ^ 2 - 6 *
      (7824238120529103 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1105_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (221 / 320 : ℝ) (553 / 800 : ℝ)) :
    (56853263 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (11614937 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1105_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1105_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1106_leftExp :
    (19924256567 / 5000000000 : ℝ) ≤ Real.exp (553 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (553 / 400 : ℝ) (1044149966273 / 1000000000000 : ℝ)
    (19924256567 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1106_rightExp :
    Real.exp (1107 / 800 : ℝ) ≤ (39898354921 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1107 / 800 : ℝ) (522095377089 / 500000000000 : ℝ)
    (39898354921 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1106_denomUpper :
    Real.exp (121888142531329153 / 10000000000000000 : ℝ) ≤ (1965779361239363 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (121888142531329153 / 10000000000000000 : ℝ) (91475118117
    / 62500000000 : ℝ) (1965779361239363 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1106_denomLower :
    (967313015698873 / 5000000000 : ℝ) ≤ Real.exp (7608024692104333 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7608024692104333 / 625000000000000 : ℝ) (292574285267 /
    200000000000 : ℝ) (967313015698873 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1106_product_lower :
    (7824235629604333 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (553 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1106_leftExp
    (by norm_num : (0 : ℝ) ≤ (19924256567 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1106_product_upper :
    Real.pi * Real.exp (1107 / 800 : ℝ) ≤ (125344392531329153 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1106_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1106_endpointLower :
    (56137169 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (553 / 800 : ℝ) (1107 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7824235629604333 / 625000000000000 : ℝ) (Real.pi * Real.exp (553 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1106_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1107 / 800 : ℝ) - (553 / 1600 : ℝ)) ≤
      (1965779361239363 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1106_denomUpper
    linarith [hpThetaJensenCell1106_product_upper]
  have hi : (1 / (1965779361239363 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1107 / 800 : ℝ) - (553 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1965779361239363 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1965779361239363 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((553 / 1600 : ℝ) - Real.pi * Real.exp (1107 / 800 : ℝ)) := by
    rw [show (553 / 1600 : ℝ) - Real.pi * Real.exp (1107 / 800 : ℝ) =
      -(Real.pi * Real.exp (1107 / 800 : ℝ) - (553 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (553 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (553 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1106_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1965779361239363 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1106_endpointUpper :
    hpThetaJensenKernelEndpointUpper (553 / 800 : ℝ) (1107 / 1600 : ℝ) ≤ (28672157 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1107 / 800 : ℝ)) (125344392531329153 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1107 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1106_product_upper
  have hD : (967313015698873 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (553 / 400 : ℝ) - (1107 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1106_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1106_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (553 / 400 : ℝ) - (1107 / 3200 : ℝ)) ≤
      (1 / (967313015698873 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (967313015698873 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1107 / 3200 : ℝ) - Real.pi * Real.exp (553 / 400 : ℝ)) ≤
      (2 / (967313015698873 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1107 / 3200 : ℝ) - Real.pi * Real.exp (553 / 400 : ℝ) =
      -(Real.pi * Real.exp (553 / 400 : ℝ) - (1107 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (125344392531329153 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (125344392531329153 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1106_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (553 / 800 : ℝ) (1107 / 1600 : ℝ)) :
    (56137169 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (28672157 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1106_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1106_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1107_leftExp :
    (39898354919 / 10000000000 : ℝ) ≤ Real.exp (1107 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1107 / 800 : ℝ) (1044190754177 / 1000000000000 : ℝ)
    (39898354919 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1107_rightExp :
    Real.exp (277 / 200 : ℝ) ≤ (39948259049 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (277 / 200 : ℝ) (261057885919 / 250000000000 : ℝ)
    (39948259049 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1107_denomUpper :
    Real.exp (122041795990525057 / 10000000000000000 : ℝ) ≤ (1996217488416919 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (122041795990525057 / 10000000000000000 : ℝ)
    (1464304832039 / 1000000000000 : ℝ) (1996217488416919 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1107_denomLower :
    (3836998620101 / 19531250 : ℝ) ≤ Real.exp (15235231578336381 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (15235231578336381 / 1250000000000000 : ℝ) (292714624333
    / 200000000000 : ℝ) (3836998620101 / 19531250 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1107_product_lower :
    (15668044078336381 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1107 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1107_leftExp
    (by norm_num : (0 : ℝ) ≤ (39898354919 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1107_product_upper :
    Real.pi * Real.exp (277 / 200 : ℝ) ≤ (125501170990525057 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1107_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1107_endpointLower :
    (13857249 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (1107 / 1600 : ℝ) (277 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (15668044078336381 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1107 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1107_product_lower
  have hD : Real.exp (Real.pi * Real.exp (277 / 200 : ℝ) - (1107 / 3200 : ℝ)) ≤
      (1996217488416919 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1107_denomUpper
    linarith [hpThetaJensenCell1107_product_upper]
  have hi : (1 / (1996217488416919 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (277 / 200 : ℝ) - (1107 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1996217488416919 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1996217488416919 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1107 / 3200 : ℝ) - Real.pi * Real.exp (277 / 200 : ℝ)) := by
    rw [show (1107 / 3200 : ℝ) - Real.pi * Real.exp (277 / 200 : ℝ) =
      -(Real.pi * Real.exp (277 / 200 : ℝ) - (1107 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1107 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1107 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1107_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1996217488416919 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1107_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1107 / 1600 : ℝ) (277 / 400 : ℝ) ≤ (7077751 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (277 / 200 : ℝ)) (125501170990525057 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (277 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1107_product_upper
  have hD : (3836998620101 / 19531250 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1107 / 800 : ℝ) - (277 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1107_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1107_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1107 / 800 : ℝ) - (277 / 800 : ℝ)) ≤
      (1 / (3836998620101 / 19531250 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3836998620101 / 19531250 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((277 / 800 : ℝ) - Real.pi * Real.exp (1107 / 800 : ℝ)) ≤
      (2 / (3836998620101 / 19531250 : ℝ) : ℝ) := by
    rw [show (277 / 800 : ℝ) - Real.pi * Real.exp (1107 / 800 : ℝ) =
      -(Real.pi * Real.exp (1107 / 800 : ℝ) - (277 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (125501170990525057 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (125501170990525057 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1107_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1107 / 1600 : ℝ) (277 / 400 : ℝ)) :
    (13857249 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7077751 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1107_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1107_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1108_leftExp :
    (19974129523 / 5000000000 : ℝ) ≤ Real.exp (277 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (277 / 200 : ℝ) (41769261747 / 40000000000 : ℝ)
    (19974129523 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1108_rightExp :
    Real.exp (1109 / 800 : ℝ) ≤ (9999556399 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1109 / 800 : ℝ) (65267020923 / 62500000000 : ℝ)
    (9999556399 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1108_denomUpper :
    Real.exp (30548911386203607 / 2500000000000000 : ℝ) ≤ (202716667095509 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (30548911386203607 / 2500000000000000 : ℝ) (1465009009571
    / 1000000000000 : ℝ) (202716667095509 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1108_denomLower :
    (997481135419973 / 5000000000 : ℝ) ≤ Real.exp (7627219127052577 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7627219127052577 / 625000000000000 : ℝ) (1464276049773 /
    1000000000000 : ℝ) (997481135419973 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1108_product_lower :
    (7843820689552577 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (277 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1108_leftExp
    (by norm_num : (0 : ℝ) ≤ (19974129523 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1108_product_upper :
    Real.pi * Real.exp (1109 / 800 : ℝ) ≤ (31414536386203607 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1108_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1108_endpointLower :
    (54728669 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (277 / 400 : ℝ) (1109 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7843820689552577 / 625000000000000 : ℝ) (Real.pi * Real.exp (277 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1108_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1109 / 800 : ℝ) - (277 / 800 : ℝ)) ≤
      (202716667095509 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1108_denomUpper
    linarith [hpThetaJensenCell1108_product_upper]
  have hi : (1 / (202716667095509 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1109 / 800 : ℝ) - (277 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (202716667095509 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (202716667095509 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((277 / 800 : ℝ) - Real.pi * Real.exp (1109 / 800 : ℝ)) := by
    rw [show (277 / 800 : ℝ) - Real.pi * Real.exp (1109 / 800 : ℝ) =
      -(Real.pi * Real.exp (1109 / 800 : ℝ) - (277 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (277 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (277 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1108_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (202716667095509 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1108_endpointUpper :
    hpThetaJensenKernelEndpointUpper (277 / 400 : ℝ) (1109 / 1600 : ℝ) ≤ (13976923 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1109 / 800 : ℝ)) (31414536386203607 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1109 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1108_product_upper
  have hD : (997481135419973 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (277 / 200 : ℝ) - (1109 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1108_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1108_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (277 / 200 : ℝ) - (1109 / 3200 : ℝ)) ≤
      (1 / (997481135419973 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (997481135419973 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1109 / 3200 : ℝ) - Real.pi * Real.exp (277 / 200 : ℝ)) ≤
      (2 / (997481135419973 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1109 / 3200 : ℝ) - Real.pi * Real.exp (277 / 200 : ℝ) =
      -(Real.pi * Real.exp (277 / 200 : ℝ) - (1109 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (31414536386203607 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (31414536386203607 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1108_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (277 / 400 : ℝ) (1109 / 1600 : ℝ)) :
    (54728669 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (13976923 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1108_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1108_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1109_leftExp :
    (19999112797 / 5000000000 : ℝ) ≤ Real.exp (1109 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1109 / 800 : ℝ) (1044272334767 / 1000000000000 : ℝ)
    (19999112797 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1109_rightExp :
    Real.exp (111 / 80 : ℝ) ≤ (500603183 / 125000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (111 / 80 : ℝ) (1044313127453 / 1000000000000 : ℝ)
    (500603183 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1109_denomUpper :
    Real.exp (1529371142990519 / 125000000000000 : ℝ) ≤ (2058636105799807 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1529371142990519 / 125000000000000 : ℝ) (732857212523 /
    500000000000 : ℝ) (2058636105799807 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1109_denomLower :
    (506472995772791 / 2500000000 : ℝ) ≤ Real.exp (7636834721269103 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7636834721269103 / 625000000000000 : ℝ) (1464980213249 /
    1000000000000 : ℝ) (506472995772791 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1109_product_lower :
    (7853631596269103 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1109 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1109_leftExp
    (by norm_num : (0 : ℝ) ≤ (19999112797 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1109_product_upper :
    Real.pi * Real.exp (111 / 80 : ℝ) ≤ (1572691455490519 / 125000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1109_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1109_endpointLower :
    (54036117 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1109 / 1600 : ℝ) (111 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7853631596269103 / 625000000000000 : ℝ) (Real.pi * Real.exp (1109 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1109_product_lower
  have hD : Real.exp (Real.pi * Real.exp (111 / 80 : ℝ) - (1109 / 3200 : ℝ)) ≤
      (2058636105799807 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1109_denomUpper
    linarith [hpThetaJensenCell1109_product_upper]
  have hi : (1 / (2058636105799807 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (111 / 80 : ℝ) - (1109 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2058636105799807 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2058636105799807 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1109 / 3200 : ℝ) - Real.pi * Real.exp (111 / 80 : ℝ)) := by
    rw [show (1109 / 3200 : ℝ) - Real.pi * Real.exp (111 / 80 : ℝ) =
      -(Real.pi * Real.exp (111 / 80 : ℝ) - (1109 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1109 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1109 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1109_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2058636105799807 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1109_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1109 / 1600 : ℝ) (111 / 160 : ℝ) ≤ (55201291 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (111 / 80 : ℝ)) (1572691455490519 / 125000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (111 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1109_product_upper
  have hD : (506472995772791 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1109 / 800 : ℝ) - (111 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell1109_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1109_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1109 / 800 : ℝ) - (111 / 320 : ℝ)) ≤
      (1 / (506472995772791 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (506472995772791 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((111 / 320 : ℝ) - Real.pi * Real.exp (1109 / 800 : ℝ)) ≤
      (2 / (506472995772791 / 2500000000 : ℝ) : ℝ) := by
    rw [show (111 / 320 : ℝ) - Real.pi * Real.exp (1109 / 800 : ℝ) =
      -(Real.pi * Real.exp (1109 / 800 : ℝ) - (111 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1572691455490519 / 125000000000000 : ℝ) ^ 2 - 6 *
      (1572691455490519 / 125000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1109_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1109 / 1600 : ℝ) (111 / 160 : ℝ)) :
    (54036117 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (55201291 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1109_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1109_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1110_leftExp :
    (20024127319 / 5000000000 : ℝ) ≤ Real.exp (111 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (111 / 80 : ℝ) (261078281863 / 250000000000 : ℝ)
    (20024127319 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1110_rightExp :
    Real.exp (1111 / 800 : ℝ) ≤ (20049173129 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1111 / 800 : ℝ) (1044353921731 / 1000000000000 : ℝ)
    (20049173129 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1110_denomUpper :
    Real.exp (61251966957854497 / 5000000000000000 : ℝ) ≤ (1045317582607183 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (61251966957854497 / 5000000000000000 : ℝ) (293284216207
    / 200000000000 : ℝ) (1045317582607183 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1110_denomLower :
    (1028670809785379 / 5000000000 : ℝ) ≤ Real.exp (7646462586543981 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7646462586543981 / 625000000000000 : ℝ) (1465685614629 /
    1000000000000 : ℝ) (1028670809785379 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1110_product_lower :
    (7863454774043981 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (111 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1110_leftExp
    (by norm_num : (0 : ℝ) ≤ (20024127319 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1110_product_upper :
    Real.pi * Real.exp (1111 / 800 : ℝ) ≤ (62986341957854497 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1110_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1110_endpointLower :
    (13337817 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (111 / 160 : ℝ) (1111 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7863454774043981 / 625000000000000 : ℝ) (Real.pi * Real.exp (111 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell1110_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1111 / 800 : ℝ) - (111 / 320 : ℝ)) ≤
      (1045317582607183 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1110_denomUpper
    linarith [hpThetaJensenCell1110_product_upper]
  have hi : (1 / (1045317582607183 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1111 / 800 : ℝ) - (111 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1045317582607183 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1045317582607183 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((111 / 320 : ℝ) - Real.pi * Real.exp (1111 / 800 : ℝ)) := by
    rw [show (111 / 320 : ℝ) - Real.pi * Real.exp (1111 / 800 : ℝ) =
      -(Real.pi * Real.exp (1111 / 800 : ℝ) - (111 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (111 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (111 / 80 : ℝ)) := by
    have h := hpThetaJensenCell1110_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1045317582607183 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1110_endpointUpper :
    hpThetaJensenKernelEndpointUpper (111 / 160 : ℝ) (1111 / 1600 : ℝ) ≤ (13625683 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1111 / 800 : ℝ)) (62986341957854497 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1111 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1110_product_upper
  have hD : (1028670809785379 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (111 / 80 : ℝ) - (1111 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1110_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1110_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (111 / 80 : ℝ) - (1111 / 3200 : ℝ)) ≤
      (1 / (1028670809785379 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1028670809785379 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1111 / 3200 : ℝ) - Real.pi * Real.exp (111 / 80 : ℝ)) ≤
      (2 / (1028670809785379 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1111 / 3200 : ℝ) - Real.pi * Real.exp (111 / 80 : ℝ) =
      -(Real.pi * Real.exp (111 / 80 : ℝ) - (1111 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (62986341957854497 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (62986341957854497 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1110_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (111 / 160 : ℝ) (1111 / 1600 : ℝ)) :
    (13337817 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (13625683 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1110_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1110_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1111_leftExp :
    (2506146641 / 625000000 : ℝ) ≤ Real.exp (1111 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1111 / 800 : ℝ) (104435392173 / 100000000000 : ℝ)
    (2506146641 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1111_rightExp :
    Real.exp (139 / 100 : ℝ) ≤ (40148500531 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (139 / 100 : ℝ) (1044394717603 / 1000000000000 : ℝ)
    (40148500531 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1111_denomUpper :
    Real.exp (122658373228685883 / 10000000000000000 : ℝ) ≤ (530793350882207 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (122658373228685883 / 10000000000000000 : ℝ)
    (366782245043 / 250000000000 : ℝ) (530793350882207 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1111_denomLower :
    (2089320547298217 / 10000000000 : ℝ) ≤ Real.exp (957012842274059 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (957012842274059 / 78125000000000 : ℝ) (1466392256499 /
    1000000000000 : ℝ) (2089320547298217 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1111_product_lower :
    (984161279774059 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (1111 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1111_leftExp
    (by norm_num : (0 : ℝ) ≤ (2506146641 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1111_product_upper :
    Real.pi * Real.exp (139 / 100 : ℝ) ≤ (126130248228685883 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1111_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1111_endpointLower :
    (102879 / 19531250 : ℝ) ≤ hpThetaTraceEndpointLower (1111 / 1600 : ℝ) (139 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (984161279774059 / 78125000000000 : ℝ) (Real.pi * Real.exp (1111 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1111_product_lower
  have hD : Real.exp (Real.pi * Real.exp (139 / 100 : ℝ) - (1111 / 3200 : ℝ)) ≤
      (530793350882207 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1111_denomUpper
    linarith [hpThetaJensenCell1111_product_upper]
  have hi : (1 / (530793350882207 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (139 / 100 : ℝ) - (1111 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (530793350882207 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (530793350882207 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1111 / 3200 : ℝ) - Real.pi * Real.exp (139 / 100 : ℝ)) := by
    rw [show (1111 / 3200 : ℝ) - Real.pi * Real.exp (139 / 100 : ℝ) =
      -(Real.pi * Real.exp (139 / 100 : ℝ) - (1111 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1111 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1111 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1111_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (530793350882207 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1111_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1111 / 1600 : ℝ) (139 / 200 : ℝ) ≤ (53811943 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (139 / 100 : ℝ)) (126130248228685883 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (139 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1111_product_upper
  have hD : (2089320547298217 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1111 / 800 : ℝ) - (139 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1111_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1111_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1111 / 800 : ℝ) - (139 / 400 : ℝ)) ≤
      (1 / (2089320547298217 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2089320547298217 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((139 / 400 : ℝ) - Real.pi * Real.exp (1111 / 800 : ℝ)) ≤
      (2 / (2089320547298217 / 10000000000 : ℝ) : ℝ) := by
    rw [show (139 / 400 : ℝ) - Real.pi * Real.exp (1111 / 800 : ℝ) =
      -(Real.pi * Real.exp (1111 / 800 : ℝ) - (139 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (126130248228685883 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (126130248228685883 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1111_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1111 / 1600 : ℝ) (139 / 200 : ℝ)) :
    (102879 / 19531250 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (53811943 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1111_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1111_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1112_leftExp :
    (40148500529 / 10000000000 : ℝ) ≤ Real.exp (139 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (139 / 100 : ℝ) (522197358801 / 500000000000 : ℝ)
    (40148500529 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1112_rightExp :
    Real.exp (1113 / 800 : ℝ) ≤ (8039743507 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1113 / 800 : ℝ) (261108878767 / 250000000000 : ℝ)
    (8039743507 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1112_denomUpper :
    Real.exp (24562601923386651 / 2000000000000000 : ℝ) ≤ (2156260554713457 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (24562601923386651 / 2000000000000000 : ℝ) (1467838125021
    / 1000000000000 : ℝ) (2156260554713457 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1112_denomLower :
    (1060919157226273 / 5000000000 : ℝ) ≤ Real.exp (15331510384237771 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (15331510384237771 / 1250000000000000 : ℝ) (146710014149
    / 100000000000 : ℝ) (1060919157226273 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1112_product_lower :
    (15766276009237771 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (139 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1112_leftExp
    (by norm_num : (0 : ℝ) ≤ (40148500529 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1112_product_upper :
    Real.pi * Real.exp (1113 / 800 : ℝ) ≤ (25257601923386651 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1112_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1112_endpointLower :
    (52004387 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (139 / 200 : ℝ) (1113 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (15766276009237771 / 1250000000000000 : ℝ) (Real.pi * Real.exp (139 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1112_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1113 / 800 : ℝ) - (139 / 400 : ℝ)) ≤
      (2156260554713457 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1112_denomUpper
    linarith [hpThetaJensenCell1112_product_upper]
  have hi : (1 / (2156260554713457 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1113 / 800 : ℝ) - (139 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2156260554713457 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2156260554713457 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((139 / 400 : ℝ) - Real.pi * Real.exp (1113 / 800 : ℝ)) := by
    rw [show (139 / 400 : ℝ) - Real.pi * Real.exp (1113 / 800 : ℝ) =
      -(Real.pi * Real.exp (1113 / 800 : ℝ) - (139 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (139 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (139 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1112_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2156260554713457 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1112_endpointUpper :
    hpThetaJensenKernelEndpointUpper (139 / 200 : ℝ) (1113 / 1600 : ℝ) ≤ (53128851 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1113 / 800 : ℝ)) (25257601923386651 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1113 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1112_product_upper
  have hD : (1060919157226273 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (139 / 100 : ℝ) - (1113 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1112_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1112_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (139 / 100 : ℝ) - (1113 / 3200 : ℝ)) ≤
      (1 / (1060919157226273 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1060919157226273 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1113 / 3200 : ℝ) - Real.pi * Real.exp (139 / 100 : ℝ)) ≤
      (2 / (1060919157226273 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1113 / 3200 : ℝ) - Real.pi * Real.exp (139 / 100 : ℝ) =
      -(Real.pi * Real.exp (139 / 100 : ℝ) - (1113 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (25257601923386651 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (25257601923386651 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1112_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (139 / 200 : ℝ) (1113 / 1600 : ℝ)) :
    (52004387 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (53128851 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1112_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1112_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1113_leftExp :
    (40198717533 / 10000000000 : ℝ) ≤ Real.exp (1113 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1113 / 800 : ℝ) (1044435515067 / 1000000000000 : ℝ)
    (40198717533 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1113_rightExp :
    Real.exp (557 / 400 : ℝ) ≤ (40248997351 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (557 / 400 : ℝ) (1044476314127 / 1000000000000 : ℝ)
    (40248997351 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1113_denomUpper :
    Real.exp (122967843334920143 / 10000000000000000 : ℝ) ≤ (547476635779879 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (122967843334920143 / 10000000000000000 : ℝ)
    (1468548518229 / 1000000000000 : ℝ) (547476635779879 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1113_denomLower :
    (5387261622651 / 25000000 : ℝ) ≤ Real.exp (15350839926491567 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (15350839926491567 / 1250000000000000 : ℝ) (146780927217
    / 100000000000 : ℝ) (5387261622651 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1113_product_lower :
    (15785996176491567 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1113 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1113_leftExp
    (by norm_num : (0 : ℝ) ≤ (40198717533 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1113_product_upper :
    Real.pi * Real.exp (557 / 400 : ℝ) ≤ (126445968334920143 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1113_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1113_endpointLower :
    (10268443 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1113 / 1600 : ℝ) (557 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (15785996176491567 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1113 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1113_product_lower
  have hD : Real.exp (Real.pi * Real.exp (557 / 400 : ℝ) - (1113 / 3200 : ℝ)) ≤
      (547476635779879 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1113_denomUpper
    linarith [hpThetaJensenCell1113_product_upper]
  have hi : (1 / (547476635779879 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (557 / 400 : ℝ) - (1113 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (547476635779879 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (547476635779879 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1113 / 3200 : ℝ) - Real.pi * Real.exp (557 / 400 : ℝ)) := by
    rw [show (1113 / 3200 : ℝ) - Real.pi * Real.exp (557 / 400 : ℝ) =
      -(Real.pi * Real.exp (557 / 400 : ℝ) - (1113 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1113 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1113 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1113_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (547476635779879 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1113_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1113 / 1600 : ℝ) (557 / 800 : ℝ) ≤ (52453383 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (557 / 400 : ℝ)) (126445968334920143 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (557 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1113_product_upper
  have hD : (5387261622651 / 25000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1113 / 800 : ℝ) - (557 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1113_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1113_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1113 / 800 : ℝ) - (557 / 1600 : ℝ)) ≤
      (1 / (5387261622651 / 25000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5387261622651 / 25000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((557 / 1600 : ℝ) - Real.pi * Real.exp (1113 / 800 : ℝ)) ≤
      (2 / (5387261622651 / 25000000 : ℝ) : ℝ) := by
    rw [show (557 / 1600 : ℝ) - Real.pi * Real.exp (1113 / 800 : ℝ) =
      -(Real.pi * Real.exp (1113 / 800 : ℝ) - (557 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (126445968334920143 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (126445968334920143 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1113_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1113 / 1600 : ℝ) (557 / 800 : ℝ)) :
    (10268443 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (52453383 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1113_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1113_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1114_leftExp :
    (10062249337 / 2500000000 : ℝ) ≤ Real.exp (557 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (557 / 400 : ℝ) (522238157063 / 500000000000 : ℝ)
    (10062249337 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1114_rightExp :
    Real.exp (223 / 160 : ℝ) ≤ (8059868011 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (223 / 160 : ℝ) (52225855739 / 50000000000 : ℝ)
    (8059868011 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1114_denomUpper :
    Real.exp (24624574924281523 / 2000000000000000 : ℝ) ≤ (139007592498773 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (24624574924281523 / 2000000000000000 : ℝ) (146926016237
    / 100000000000 : ℝ) (139007592498773 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1114_denomLower :
    (547132367092943 / 2500000000 : ℝ) ≤ Real.exp (3842548533640563 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3842548533640563 / 312500000000000 : ℝ) (45891239099 /
    31250000000 : ℝ) (547132367092943 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1114_product_lower :
    (3951435252390563 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (557 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1114_leftExp
    (by norm_num : (0 : ℝ) ≤ (10062249337 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1114_product_upper :
    Real.pi * Real.exp (223 / 160 : ℝ) ≤ (25320824924281523 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1114_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1114_endpointLower :
    (2534373 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (557 / 800 : ℝ) (223 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3951435252390563 / 312500000000000 : ℝ) (Real.pi * Real.exp (557 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1114_product_lower
  have hD : Real.exp (Real.pi * Real.exp (223 / 160 : ℝ) - (557 / 1600 : ℝ)) ≤
      (139007592498773 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1114_denomUpper
    linarith [hpThetaJensenCell1114_product_upper]
  have hi : (1 / (139007592498773 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (223 / 160 : ℝ) - (557 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (139007592498773 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (139007592498773 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((557 / 1600 : ℝ) - Real.pi * Real.exp (223 / 160 : ℝ)) := by
    rw [show (557 / 1600 : ℝ) - Real.pi * Real.exp (223 / 160 : ℝ) =
      -(Real.pi * Real.exp (223 / 160 : ℝ) - (557 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (557 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (557 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1114_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (139007592498773 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1114_endpointUpper :
    hpThetaJensenKernelEndpointUpper (557 / 800 : ℝ) (223 / 320 : ℝ) ≤ (51785469 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (223 / 160 : ℝ)) (25320824924281523 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (223 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1114_product_upper
  have hD : (547132367092943 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (557 / 400 : ℝ) - (223 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1114_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1114_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (557 / 400 : ℝ) - (223 / 640 : ℝ)) ≤
      (1 / (547132367092943 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (547132367092943 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((223 / 640 : ℝ) - Real.pi * Real.exp (557 / 400 : ℝ)) ≤
      (2 / (547132367092943 / 2500000000 : ℝ) : ℝ) := by
    rw [show (223 / 640 : ℝ) - Real.pi * Real.exp (557 / 400 : ℝ) =
      -(Real.pi * Real.exp (557 / 400 : ℝ) - (223 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (25320824924281523 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (25320824924281523 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1114_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (557 / 800 : ℝ) (223 / 320 : ℝ)) :
    (2534373 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (51785469 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1114_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1114_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1115_leftExp :
    (40299340053 / 10000000000 : ℝ) ≤ Real.exp (223 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (223 / 160 : ℝ) (1044517114779 / 1000000000000 : ℝ)
    (40299340053 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1115_rightExp :
    Real.exp (279 / 200 : ℝ) ≤ (40349745727 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (279 / 200 : ℝ) (1044557917027 / 1000000000000 : ℝ)
    (40349745727 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1115_denomUpper :
    Real.exp (123278103727723111 / 10000000000000000 : ℝ) ≤ (1129457836913077 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (123278103727723111 / 10000000000000000 : ℝ)
    (367493265021 / 250000000000 : ℝ) (1129457836913077 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1115_denomLower :
    (555680719861899 / 2500000000 : ℝ) ≤ Real.exp (15389573039473047 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (15389573039473047 / 1250000000000000 : ℝ) (91826955069 /
    62500000000 : ℝ) (555680719861899 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1115_product_lower :
    (15825510539473047 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (223 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1115_leftExp
    (by norm_num : (0 : ℝ) ≤ (40299340053 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1115_product_upper :
    Real.pi * Real.exp (279 / 200 : ℝ) ≤ (126762478727723111 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1115_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1115_endpointLower :
    (25020027 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (223 / 320 : ℝ) (279 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (15825510539473047 / 1250000000000000 : ℝ) (Real.pi * Real.exp (223 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1115_product_lower
  have hD : Real.exp (Real.pi * Real.exp (279 / 200 : ℝ) - (223 / 640 : ℝ)) ≤
      (1129457836913077 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1115_denomUpper
    linarith [hpThetaJensenCell1115_product_upper]
  have hi : (1 / (1129457836913077 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (279 / 200 : ℝ) - (223 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1129457836913077 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1129457836913077 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((223 / 640 : ℝ) - Real.pi * Real.exp (279 / 200 : ℝ)) := by
    rw [show (223 / 640 : ℝ) - Real.pi * Real.exp (279 / 200 : ℝ) =
      -(Real.pi * Real.exp (279 / 200 : ℝ) - (223 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (223 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (223 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1115_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1129457836913077 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1115_endpointUpper :
    hpThetaJensenKernelEndpointUpper (223 / 320 : ℝ) (279 / 400 : ℝ) ≤ (25562519 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (279 / 200 : ℝ)) (126762478727723111 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (279 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1115_product_upper
  have hD : (555680719861899 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (223 / 160 : ℝ) - (279 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1115_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1115_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (223 / 160 : ℝ) - (279 / 800 : ℝ)) ≤
      (1 / (555680719861899 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (555680719861899 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((279 / 800 : ℝ) - Real.pi * Real.exp (223 / 160 : ℝ)) ≤
      (2 / (555680719861899 / 2500000000 : ℝ) : ℝ) := by
    rw [show (279 / 800 : ℝ) - Real.pi * Real.exp (223 / 160 : ℝ) =
      -(Real.pi * Real.exp (223 / 160 : ℝ) - (279 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (126762478727723111 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (126762478727723111 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1115_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (223 / 320 : ℝ) (279 / 400 : ℝ)) :
    (25020027 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (25562519 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1115_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1115_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1116_leftExp :
    (1613989829 / 400000000 : ℝ) ≤ Real.exp (279 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (279 / 200 : ℝ) (522278958513 / 500000000000 : ℝ)
    (1613989829 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1116_rightExp :
    Real.exp (1117 / 800 : ℝ) ≤ (20200107223 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1117 / 800 : ℝ) (261149680217 / 250000000000 : ℝ)
    (20200107223 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1116_denomUpper :
    Real.exp (61716765451026239 / 5000000000000000 : ℝ) ≤ (2294299630955683 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (61716765451026239 / 5000000000000000 : ℝ) (1470687214003
    / 1000000000000 : ℝ) (2294299630955683 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1116_denomLower :
    (564373795558079 / 2500000000 : ℝ) ≤ Real.exp (616359066858471 / 50000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (616359066858471 / 50000000000000 : ℝ) (734972082287 /
    500000000000 : ℝ) (564373795558079 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1116_product_lower :
    (633812191858471 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (279 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1116_leftExp
    (by norm_num : (0 : ℝ) ≤ (1613989829 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1116_product_upper :
    Real.pi * Real.exp (1117 / 800 : ℝ) ≤ (63460515451026239 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1116_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1116_endpointLower :
    (24699963 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (279 / 400 : ℝ) (1117 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (633812191858471 / 50000000000000 : ℝ) (Real.pi * Real.exp (279 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1116_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1117 / 800 : ℝ) - (279 / 800 : ℝ)) ≤
      (2294299630955683 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1116_denomUpper
    linarith [hpThetaJensenCell1116_product_upper]
  have hi : (1 / (2294299630955683 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1117 / 800 : ℝ) - (279 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2294299630955683 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2294299630955683 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((279 / 800 : ℝ) - Real.pi * Real.exp (1117 / 800 : ℝ)) := by
    rw [show (279 / 800 : ℝ) - Real.pi * Real.exp (1117 / 800 : ℝ) =
      -(Real.pi * Real.exp (1117 / 800 : ℝ) - (279 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (279 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (279 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1116_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2294299630955683 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1116_endpointUpper :
    hpThetaJensenKernelEndpointUpper (279 / 400 : ℝ) (1117 / 1600 : ℝ) ≤ (50472019 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1117 / 800 : ℝ)) (63460515451026239 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1117 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1116_product_upper
  have hD : (564373795558079 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (279 / 200 : ℝ) - (1117 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1116_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1116_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (279 / 200 : ℝ) - (1117 / 3200 : ℝ)) ≤
      (1 / (564373795558079 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (564373795558079 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1117 / 3200 : ℝ) - Real.pi * Real.exp (279 / 200 : ℝ)) ≤
      (2 / (564373795558079 / 2500000000 : ℝ) : ℝ) := by
    rw [show (1117 / 3200 : ℝ) - Real.pi * Real.exp (279 / 200 : ℝ) =
      -(Real.pi * Real.exp (279 / 200 : ℝ) - (1117 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (63460515451026239 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (63460515451026239 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1116_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (279 / 400 : ℝ) (1117 / 1600 : ℝ)) :
    (24699963 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (50472019 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1116_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1116_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1117_leftExp :
    (10100053611 / 2500000000 : ℝ) ≤ Real.exp (1117 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1117 / 800 : ℝ) (1044598720867 / 1000000000000 : ℝ)
    (10100053611 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1117_rightExp :
    Real.exp (559 / 400 : ℝ) ≤ (4045074629 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (559 / 400 : ℝ) (522319763151 / 500000000000 : ℝ)
    (4045074629 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1117_denomUpper :
    Real.exp (12358915638943997 / 1000000000000000 : ℝ) ≤ (46605681185297 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (12358915638943997 / 1000000000000000 : ℝ) (367850656687
    / 250000000000 : ℝ) (46605681185297 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1117_denomLower :
    (573214219257323 / 2500000000 : ℝ) ≤ Real.exp (3857101265486089 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3857101265486089 / 312500000000000 : ℝ) (1470658304223 /
    1000000000000 : ℝ) (573214219257323 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1117_product_lower :
    (3966280952986089 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (1117 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1117_leftExp
    (by norm_num : (0 : ℝ) ≤ (10100053611 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1117_product_upper :
    Real.pi * Real.exp (559 / 400 : ℝ) ≤ (12707978138943997 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1117_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1117_endpointLower :
    (48767009 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1117 / 1600 : ℝ) (559 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3966280952986089 / 312500000000000 : ℝ) (Real.pi * Real.exp (1117 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1117_product_lower
  have hD : Real.exp (Real.pi * Real.exp (559 / 400 : ℝ) - (1117 / 3200 : ℝ)) ≤
      (46605681185297 / 200000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1117_denomUpper
    linarith [hpThetaJensenCell1117_product_upper]
  have hi : (1 / (46605681185297 / 200000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (559 / 400 : ℝ) - (1117 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (46605681185297 / 200000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (46605681185297 / 200000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1117 / 3200 : ℝ) - Real.pi * Real.exp (559 / 400 : ℝ)) := by
    rw [show (1117 / 3200 : ℝ) - Real.pi * Real.exp (559 / 400 : ℝ) =
      -(Real.pi * Real.exp (559 / 400 : ℝ) - (1117 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1117 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1117 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1117_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (46605681185297 / 200000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1117_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1117 / 1600 : ℝ) (559 / 800 : ℝ) ≤ (24913171 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (559 / 400 : ℝ)) (12707978138943997 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (559 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1117_product_upper
  have hD : (573214219257323 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1117 / 800 : ℝ) - (559 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1117_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1117_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1117 / 800 : ℝ) - (559 / 1600 : ℝ)) ≤
      (1 / (573214219257323 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (573214219257323 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((559 / 1600 : ℝ) - Real.pi * Real.exp (1117 / 800 : ℝ)) ≤
      (2 / (573214219257323 / 2500000000 : ℝ) : ℝ) := by
    rw [show (559 / 1600 : ℝ) - Real.pi * Real.exp (1117 / 800 : ℝ) =
      -(Real.pi * Real.exp (1117 / 800 : ℝ) - (559 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (12707978138943997 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (12707978138943997 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1117_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1117 / 1600 : ℝ) (559 / 800 : ℝ)) :
    (48767009 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (24913171 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1117_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1117_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1118_leftExp :
    (40450746287 / 10000000000 : ℝ) ≤ Real.exp (559 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (559 / 400 : ℝ) (1044639526301 / 1000000000000 : ℝ)
    (40450746287 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1118_rightExp :
    Real.exp (1119 / 800 : ℝ) ≤ (20250670669 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1119 / 800 : ℝ) (1044680333331 / 1000000000000 : ℝ)
    (20250670669 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1118_denomUpper :
    Real.exp (61872490219035717 / 5000000000000000 : ℝ) ≤ (473375974758201 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (61872490219035717 / 5000000000000000 : ℝ) (736059650479
    / 500000000000 : ℝ) (473375974758201 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1118_denomLower :
    (2328818664232363 / 10000000000 : ℝ) ≤ Real.exp (15447858241158613 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (15447858241158613 / 1250000000000000 : ℝ) (1471373702657
    / 1000000000000 : ℝ) (2328818664232363 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1118_product_lower :
    (15884967616158613 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (559 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1118_leftExp
    (by norm_num : (0 : ℝ) ≤ (40450746287 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1118_product_upper :
    Real.pi * Real.exp (1119 / 800 : ℝ) ≤ (63619365219035717 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1118_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1118_endpointLower :
    (48141233 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (559 / 800 : ℝ) (1119 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (15884967616158613 / 1250000000000000 : ℝ) (Real.pi * Real.exp (559 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1118_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1119 / 800 : ℝ) - (559 / 1600 : ℝ)) ≤
      (473375974758201 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1118_denomUpper
    linarith [hpThetaJensenCell1118_product_upper]
  have hi : (1 / (473375974758201 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1119 / 800 : ℝ) - (559 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (473375974758201 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (473375974758201 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((559 / 1600 : ℝ) - Real.pi * Real.exp (1119 / 800 : ℝ)) := by
    rw [show (559 / 1600 : ℝ) - Real.pi * Real.exp (1119 / 800 : ℝ) =
      -(Real.pi * Real.exp (1119 / 800 : ℝ) - (559 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (559 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (559 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1118_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (473375974758201 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1118_endpointUpper :
    hpThetaJensenKernelEndpointUpper (559 / 800 : ℝ) (1119 / 1600 : ℝ) ≤ (24593969 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1119 / 800 : ℝ)) (63619365219035717 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1119 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1118_product_upper
  have hD : (2328818664232363 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (559 / 400 : ℝ) - (1119 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1118_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1118_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (559 / 400 : ℝ) - (1119 / 3200 : ℝ)) ≤
      (1 / (2328818664232363 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2328818664232363 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1119 / 3200 : ℝ) - Real.pi * Real.exp (559 / 400 : ℝ)) ≤
      (2 / (2328818664232363 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1119 / 3200 : ℝ) - Real.pi * Real.exp (559 / 400 : ℝ) =
      -(Real.pi * Real.exp (559 / 400 : ℝ) - (1119 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (63619365219035717 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (63619365219035717 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1118_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (559 / 800 : ℝ) (1119 / 1600 : ℝ)) :
    (48141233 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (24593969 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1118_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1118_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1119_leftExp :
    (5062667667 / 1250000000 : ℝ) ≤ Real.exp (1119 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1119 / 800 : ℝ) (104468033333 / 100000000000 : ℝ)
    (5062667667 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1119_rightExp :
    Real.exp (7 / 5 : ℝ) ≤ (40551999669 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7 / 5 : ℝ) (1044721141953 / 1000000000000 : ℝ)
    (40551999669 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1119_denomUpper :
    Real.exp (123901003296132717 / 10000000000000000 : ℝ) ≤ (2404098200545709 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (123901003296132717 / 10000000000000000 : ℝ)
    (736418619641 / 500000000000 : ℝ) (2404098200545709 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1119_denomLower :
    (2365391454388163 / 10000000000 : ℝ) ≤ Real.exp (1933417030163233 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1933417030163233 / 156250000000000 : ℝ) (736045181281 /
    500000000000 : ℝ) (2365391454388163 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1119_product_lower :
    (1988104530163233 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (1119 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1119_leftExp
    (by norm_num : (0 : ℝ) ≤ (5062667667 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1119_product_upper :
    Real.pi * Real.exp (7 / 5 : ℝ) ≤ (127397878296132717 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1119_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1119_endpointLower :
    (4752253 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1119 / 1600 : ℝ) (7 / 10 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1988104530163233 / 156250000000000 : ℝ) (Real.pi * Real.exp (1119 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1119_product_lower
  have hD : Real.exp (Real.pi * Real.exp (7 / 5 : ℝ) - (1119 / 3200 : ℝ)) ≤
      (2404098200545709 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1119_denomUpper
    linarith [hpThetaJensenCell1119_product_upper]
  have hi : (1 / (2404098200545709 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (7 / 5 : ℝ) - (1119 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2404098200545709 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2404098200545709 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1119 / 3200 : ℝ) - Real.pi * Real.exp (7 / 5 : ℝ)) := by
    rw [show (1119 / 3200 : ℝ) - Real.pi * Real.exp (7 / 5 : ℝ) =
      -(Real.pi * Real.exp (7 / 5 : ℝ) - (1119 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1119 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1119 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1119_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2404098200545709 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1119_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1119 / 1600 : ℝ) (7 / 10 : ℝ) ≤ (24278369 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (7 / 5 : ℝ)) (127397878296132717 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (7 / 10 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1119_product_upper
  have hD : (2365391454388163 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1119 / 800 : ℝ) - (7 / 20 : ℝ)) := by
    apply le_trans hpThetaJensenCell1119_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1119_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1119 / 800 : ℝ) - (7 / 20 : ℝ)) ≤
      (1 / (2365391454388163 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2365391454388163 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((7 / 20 : ℝ) - Real.pi * Real.exp (1119 / 800 : ℝ)) ≤
      (2 / (2365391454388163 / 10000000000 : ℝ) : ℝ) := by
    rw [show (7 / 20 : ℝ) - Real.pi * Real.exp (1119 / 800 : ℝ) =
      -(Real.pi * Real.exp (1119 / 800 : ℝ) - (7 / 20 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (127397878296132717 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (127397878296132717 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1119_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1119 / 1600 : ℝ) (7 / 10 : ℝ)) :
    (4752253 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (24278369 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1119_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1119_endpointUpper

def hpThetaJensenCellsBatch055Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (12111029 / 2000000000 : ℝ)
  | 1 => (5979833 / 1000000000 : ℝ)
  | 2 => (5904981 / 1000000000 : ℝ)
  | 3 => (58309509 / 10000000000 : ℝ)
  | 4 => (7197169 / 1250000000 : ℝ)
  | 5 => (56853263 / 10000000000 : ℝ)
  | 6 => (56137169 / 10000000000 : ℝ)
  | 7 => (13857249 / 2500000000 : ℝ)
  | 8 => (54728669 / 10000000000 : ℝ)
  | 9 => (54036117 / 10000000000 : ℝ)
  | 10 => (13337817 / 2500000000 : ℝ)
  | 11 => (102879 / 19531250 : ℝ)
  | 12 => (52004387 / 10000000000 : ℝ)
  | 13 => (10268443 / 2000000000 : ℝ)
  | 14 => (2534373 / 500000000 : ℝ)
  | 15 => (25020027 / 5000000000 : ℝ)
  | 16 => (24699963 / 5000000000 : ℝ)
  | 17 => (48767009 / 10000000000 : ℝ)
  | 18 => (48141233 / 10000000000 : ℝ)
  | 19 => (4752253 / 1000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch055Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1932817 / 312500000 : ℝ)
  | 1 => (61078317 / 10000000000 : ℝ)
  | 2 => (30157467 / 5000000000 : ℝ)
  | 3 => (59559919 / 10000000000 : ℝ)
  | 4 => (11762639 / 2000000000 : ℝ)
  | 5 => (11614937 / 2000000000 : ℝ)
  | 6 => (28672157 / 5000000000 : ℝ)
  | 7 => (7077751 / 1250000000 : ℝ)
  | 8 => (13976923 / 2500000000 : ℝ)
  | 9 => (55201291 / 10000000000 : ℝ)
  | 10 => (13625683 / 2500000000 : ℝ)
  | 11 => (53811943 / 10000000000 : ℝ)
  | 12 => (53128851 / 10000000000 : ℝ)
  | 13 => (52453383 / 10000000000 : ℝ)
  | 14 => (51785469 / 10000000000 : ℝ)
  | 15 => (25562519 / 5000000000 : ℝ)
  | 16 => (50472019 / 10000000000 : ℝ)
  | 17 => (24913171 / 5000000000 : ℝ)
  | 18 => (24593969 / 5000000000 : ℝ)
  | 19 => (24278369 / 5000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch055_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1100 : ℝ) + (j.val : ℝ)) / 1600)
      (((1100 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch055Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch055Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1100_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1101_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1102_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1103_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1104_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1105_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1106_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1107_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1108_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1109_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1110_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1111_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1112_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1113_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1114_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1115_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1116_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1117_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1118_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1119_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper] at h ⊢
    exact h

end HodgeProofHP
