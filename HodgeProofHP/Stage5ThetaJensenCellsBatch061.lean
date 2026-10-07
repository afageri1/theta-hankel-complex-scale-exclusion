import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1220_leftExp :
    (11487858923 / 2500000000 : ℝ) ≤ Real.exp (61 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (61 / 40 : ℝ) (1048810064891 / 1000000000000 : ℝ)
    (11487858923 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1220_rightExp :
    Real.exp (1221 / 800 : ℝ) ≤ (5751113863 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1221 / 800 : ℝ) (262212758709 / 250000000000 : ℝ)
    (5751113863 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1220_denomUpper :
    Real.exp (17591096554203759 / 1250000000000000 : ℝ) ≤ (12935193544769427 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (17591096554203759 / 1250000000000000 : ℝ) (1552361645859
    / 1000000000000 : ℝ) (12935193544769427 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1220_denomLower :
    (2539939846893083 / 2000000000 : ℝ) ≤ Real.exp (4392032429953177 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4392032429953177 / 312500000000000 : ℝ) (1551470580873 /
    1000000000000 : ℝ) (2539939846893083 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1220_product_lower :
    (4511270711203177 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (61 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1220_leftExp
    (by norm_num : (0 : ℝ) ≤ (11487858923 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1220_product_upper :
    Real.pi * Real.exp (1221 / 800 : ℝ) ≤ (18067659054203759 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1220_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1220_endpointLower :
    (180463 / 156250000 : ℝ) ≤ hpThetaTraceEndpointLower (61 / 80 : ℝ) (1221 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4511270711203177 / 312500000000000 : ℝ) (Real.pi * Real.exp (61 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell1220_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1221 / 800 : ℝ) - (61 / 160 : ℝ)) ≤
      (12935193544769427 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1220_denomUpper
    linarith [hpThetaJensenCell1220_product_upper]
  have hi : (1 / (12935193544769427 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1221 / 800 : ℝ) - (61 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (12935193544769427 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (12935193544769427 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((61 / 160 : ℝ) - Real.pi * Real.exp (1221 / 800 : ℝ)) := by
    rw [show (61 / 160 : ℝ) - Real.pi * Real.exp (1221 / 800 : ℝ) =
      -(Real.pi * Real.exp (1221 / 800 : ℝ) - (61 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (61 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (61 / 40 : ℝ)) := by
    have h := hpThetaJensenCell1220_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (12935193544769427 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1220_endpointUpper :
    hpThetaJensenKernelEndpointUpper (61 / 80 : ℝ) (1221 / 1600 : ℝ) ≤ (5913013 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1221 / 800 : ℝ)) (18067659054203759 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1221 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1220_product_upper
  have hD : (2539939846893083 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (61 / 40 : ℝ) - (1221 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1220_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1220_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (61 / 40 : ℝ) - (1221 / 3200 : ℝ)) ≤
      (1 / (2539939846893083 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2539939846893083 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1221 / 3200 : ℝ) - Real.pi * Real.exp (61 / 40 : ℝ)) ≤
      (2 / (2539939846893083 / 2000000000 : ℝ) : ℝ) := by
    rw [show (1221 / 3200 : ℝ) - Real.pi * Real.exp (61 / 40 : ℝ) =
      -(Real.pi * Real.exp (61 / 40 : ℝ) - (1221 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (18067659054203759 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (18067659054203759 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1220_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (61 / 80 : ℝ) (1221 / 1600 : ℝ)) :
    (180463 / 156250000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5913013 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1220_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1220_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1221_leftExp :
    (23004455451 / 5000000000 : ℝ) ≤ Real.exp (1221 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1221 / 800 : ℝ) (209770206967 / 200000000000 : ℝ)
    (23004455451 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1221_rightExp :
    Real.exp (611 / 400 : ℝ) ≤ (46066458001 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (611 / 400 : ℝ) (1048892006379 / 1000000000000 : ℝ)
    (46066458001 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1221_denomUpper :
    Real.exp (140906436990735593 / 10000000000000000 : ℝ) ≤ (6583529854556243 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (140906436990735593 / 10000000000000000 : ℝ)
    (1553223759049 / 1000000000000 : ℝ) (6583529854556243 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1221_denomLower :
    (6463526045049471 / 5000000000 : ℝ) ≤ Real.exp (8795154776152249 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8795154776152249 / 625000000000000 : ℝ) (1552331103369 /
    1000000000000 : ℝ) (6463526045049471 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1221_product_lower :
    (9033826651152249 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1221 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1221_leftExp
    (by norm_num : (0 : ℝ) ≤ (23004455451 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1221_product_upper :
    Real.pi * Real.exp (611 / 400 : ℝ) ≤ (144722061990735593 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1221_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1221_endpointLower :
    (11376297 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1221 / 1600 : ℝ) (611 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9033826651152249 / 625000000000000 : ℝ) (Real.pi * Real.exp (1221 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1221_product_lower
  have hD : Real.exp (Real.pi * Real.exp (611 / 400 : ℝ) - (1221 / 3200 : ℝ)) ≤
      (6583529854556243 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1221_denomUpper
    linarith [hpThetaJensenCell1221_product_upper]
  have hi : (1 / (6583529854556243 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (611 / 400 : ℝ) - (1221 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (6583529854556243 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (6583529854556243 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1221 / 3200 : ℝ) - Real.pi * Real.exp (611 / 400 : ℝ)) := by
    rw [show (1221 / 3200 : ℝ) - Real.pi * Real.exp (611 / 400 : ℝ) =
      -(Real.pi * Real.exp (611 / 400 : ℝ) - (1221 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1221 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1221 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1221_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (6583529854556243 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1221_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1221 / 1600 : ℝ) (611 / 800 : ℝ) ≤ (11648803 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (611 / 400 : ℝ)) (144722061990735593 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (611 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1221_product_upper
  have hD : (6463526045049471 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1221 / 800 : ℝ) - (611 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1221_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1221_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1221 / 800 : ℝ) - (611 / 1600 : ℝ)) ≤
      (1 / (6463526045049471 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6463526045049471 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((611 / 1600 : ℝ) - Real.pi * Real.exp (1221 / 800 : ℝ)) ≤
      (2 / (6463526045049471 / 5000000000 : ℝ) : ℝ) := by
    rw [show (611 / 1600 : ℝ) - Real.pi * Real.exp (1221 / 800 : ℝ) =
      -(Real.pi * Real.exp (1221 / 800 : ℝ) - (611 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (144722061990735593 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (144722061990735593 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1221_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1221 / 1600 : ℝ) (611 / 800 : ℝ)) :
    (11376297 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (11648803 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1221_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1221_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1222_leftExp :
    (46066457999 / 10000000000 : ℝ) ≤ Real.exp (611 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (611 / 400 : ℝ) (524446003189 / 500000000000 : ℝ)
    (46066457999 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1222_rightExp :
    Real.exp (1223 / 800 : ℝ) ≤ (46124077079 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1223 / 800 : ℝ) (262233244881 / 250000000000 : ℝ)
    (46124077079 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1222_denomUpper :
    Real.exp (141084327682846847 / 10000000000000000 : ℝ) ≤ (670169260949301 / 500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (141084327682846847 / 10000000000000000 : ℝ) (48565232789
    / 31250000000 : ℝ) (670169260949301 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1222_denomLower :
    (3289693060360081 / 2500000000 : ℝ) ≤ Real.exp (17612517614749301 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (17612517614749301 / 1250000000000000 : ℝ) (776596599659
    / 500000000000 : ℝ) (3289693060360081 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1222_product_lower :
    (18090251989749301 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (611 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1222_leftExp
    (by norm_num : (0 : ℝ) ≤ (46066457999 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1222_product_upper :
    Real.pi * Real.exp (1223 / 800 : ℝ) ≤ (144903077682846847 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1222_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1222_endpointLower :
    (11205307 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (611 / 800 : ℝ) (1223 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (18090251989749301 / 1250000000000000 : ℝ) (Real.pi * Real.exp (611 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1222_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1223 / 800 : ℝ) - (611 / 1600 : ℝ)) ≤
      (670169260949301 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1222_denomUpper
    linarith [hpThetaJensenCell1222_product_upper]
  have hi : (1 / (670169260949301 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1223 / 800 : ℝ) - (611 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (670169260949301 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (670169260949301 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((611 / 1600 : ℝ) - Real.pi * Real.exp (1223 / 800 : ℝ)) := by
    rw [show (611 / 1600 : ℝ) - Real.pi * Real.exp (1223 / 800 : ℝ) =
      -(Real.pi * Real.exp (1223 / 800 : ℝ) - (611 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (611 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (611 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1222_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (670169260949301 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1222_endpointUpper :
    hpThetaJensenKernelEndpointUpper (611 / 800 : ℝ) (1223 / 1600 : ℝ) ≤ (458959 / 400000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1223 / 800 : ℝ)) (144903077682846847 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1223 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1222_product_upper
  have hD : (3289693060360081 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (611 / 400 : ℝ) - (1223 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1222_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1222_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (611 / 400 : ℝ) - (1223 / 3200 : ℝ)) ≤
      (1 / (3289693060360081 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3289693060360081 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1223 / 3200 : ℝ) - Real.pi * Real.exp (611 / 400 : ℝ)) ≤
      (2 / (3289693060360081 / 2500000000 : ℝ) : ℝ) := by
    rw [show (1223 / 3200 : ℝ) - Real.pi * Real.exp (611 / 400 : ℝ) =
      -(Real.pi * Real.exp (611 / 400 : ℝ) - (1223 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (144903077682846847 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (144903077682846847 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1222_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (611 / 800 : ℝ) (1223 / 1600 : ℝ)) :
    (11205307 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (458959 / 400000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1222_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1222_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1223_leftExp :
    (46124077077 / 10000000000 : ℝ) ≤ Real.exp (1223 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1223 / 800 : ℝ) (1048932979523 / 1000000000000 : ℝ)
    (46124077077 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1223_rightExp :
    Real.exp (153 / 100 : ℝ) ≤ (1443180257 / 312500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (153 / 100 : ℝ) (262243488567 / 250000000000 : ℝ)
    (1443180257 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1223_denomUpper :
    Real.exp (4414451399379401 / 312500000000000 : ℝ) ≤ (2728852252905143 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4414451399379401 / 312500000000000 : ℝ) (777476359933 /
    500000000000 : ℝ) (2728852252905143 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1223_denomLower :
    (1674368616085837 / 1250000000 : ℝ) ≤ Real.exp (17634753944060823 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (17634753944060823 / 1250000000000000 : ℝ) (388514218061
    / 250000000000 : ℝ) (1674368616085837 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1223_product_lower :
    (18112878944060823 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1223 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1223_leftExp
    (by norm_num : (0 : ℝ) ≤ (46124077077 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1223_product_upper :
    Real.pi * Real.exp (153 / 100 : ℝ) ≤ (4533884993129401 / 312500000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1223_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1223_endpointLower :
    (2207327 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1223 / 1600 : ℝ) (153 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (18112878944060823 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1223 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1223_product_lower
  have hD : Real.exp (Real.pi * Real.exp (153 / 100 : ℝ) - (1223 / 3200 : ℝ)) ≤
      (2728852252905143 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1223_denomUpper
    linarith [hpThetaJensenCell1223_product_upper]
  have hi : (1 / (2728852252905143 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (153 / 100 : ℝ) - (1223 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2728852252905143 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2728852252905143 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1223 / 3200 : ℝ) - Real.pi * Real.exp (153 / 100 : ℝ)) := by
    rw [show (1223 / 3200 : ℝ) - Real.pi * Real.exp (153 / 100 : ℝ) =
      -(Real.pi * Real.exp (153 / 100 : ℝ) - (1223 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1223 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1223 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1223_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2728852252905143 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1223_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1223 / 1600 : ℝ) (153 / 200 : ℝ) ≤ (11301513 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (153 / 100 : ℝ)) (4533884993129401 / 312500000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (153 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1223_product_upper
  have hD : (1674368616085837 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1223 / 800 : ℝ) - (153 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1223_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1223_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1223 / 800 : ℝ) - (153 / 400 : ℝ)) ≤
      (1 / (1674368616085837 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1674368616085837 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((153 / 400 : ℝ) - Real.pi * Real.exp (1223 / 800 : ℝ)) ≤
      (2 / (1674368616085837 / 1250000000 : ℝ) : ℝ) := by
    rw [show (153 / 400 : ℝ) - Real.pi * Real.exp (1223 / 800 : ℝ) =
      -(Real.pi * Real.exp (1223 / 800 : ℝ) - (153 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4533884993129401 / 312500000000000 : ℝ) ^ 2 - 6 *
      (4533884993129401 / 312500000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1223_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1223 / 1600 : ℝ) (153 / 200 : ℝ)) :
    (2207327 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (11301513 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1223_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1223_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1224_leftExp :
    (46181768221 / 10000000000 : ℝ) ≤ Real.exp (153 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (153 / 100 : ℝ) (1048973954267 / 1000000000000 : ℝ)
    (46181768221 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1224_rightExp :
    Real.exp (49 / 32 : ℝ) ≤ (46239531529 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (49 / 32 : ℝ) (524507465307 / 500000000000 : ℝ)
    (46239531529 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1224_denomUpper :
    Real.exp (141440788574785697 / 10000000000000000 : ℝ) ≤ (1388978103628153 / 1000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (141440788574785697 / 10000000000000000 : ℝ)
    (155581957443 / 100000000000 : ℝ) (1388978103628153 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1224_denomLower :
    (3408918320075041 / 2500000000 : ℝ) ≤ Real.exp (17657018573618479 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (17657018573618479 / 1250000000000000 : ℝ) (777461062771
    / 500000000000 : ℝ) (3408918320075041 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1224_product_lower :
    (18135534198618479 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (153 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1224_leftExp
    (by norm_num : (0 : ℝ) ≤ (46181768221 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1224_product_upper :
    Real.pi * Real.exp (49 / 32 : ℝ) ≤ (145265788574785697 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1224_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1224_endpointLower :
    (5435127 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (153 / 200 : ℝ) (49 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (18135534198618479 / 1250000000000000 : ℝ) (Real.pi * Real.exp (153 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1224_product_lower
  have hD : Real.exp (Real.pi * Real.exp (49 / 32 : ℝ) - (153 / 400 : ℝ)) ≤
      (1388978103628153 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1224_denomUpper
    linarith [hpThetaJensenCell1224_product_upper]
  have hi : (1 / (1388978103628153 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (49 / 32 : ℝ) - (153 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1388978103628153 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1388978103628153 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((153 / 400 : ℝ) - Real.pi * Real.exp (49 / 32 : ℝ)) := by
    rw [show (153 / 400 : ℝ) - Real.pi * Real.exp (49 / 32 : ℝ) =
      -(Real.pi * Real.exp (49 / 32 : ℝ) - (153 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (153 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (153 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1224_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1388978103628153 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1224_endpointUpper :
    hpThetaJensenKernelEndpointUpper (153 / 200 : ℝ) (49 / 64 : ℝ) ≤ (11131389 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (49 / 32 : ℝ)) (145265788574785697 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (49 / 64 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1224_product_upper
  have hD : (3408918320075041 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (153 / 100 : ℝ) - (49 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell1224_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1224_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (153 / 100 : ℝ) - (49 / 128 : ℝ)) ≤
      (1 / (3408918320075041 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3408918320075041 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((49 / 128 : ℝ) - Real.pi * Real.exp (153 / 100 : ℝ)) ≤
      (2 / (3408918320075041 / 2500000000 : ℝ) : ℝ) := by
    rw [show (49 / 128 : ℝ) - Real.pi * Real.exp (153 / 100 : ℝ) =
      -(Real.pi * Real.exp (153 / 100 : ℝ) - (49 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (145265788574785697 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (145265788574785697 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1224_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (153 / 200 : ℝ) (49 / 64 : ℝ)) :
    (5435127 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (11131389 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1224_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1224_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1225_leftExp :
    (46239531527 / 10000000000 : ℝ) ≤ Real.exp (49 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (49 / 32 : ℝ) (1049014930613 / 1000000000000 : ℝ)
    (46239531527 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1225_rightExp :
    Real.exp (613 / 400 : ℝ) ≤ (46297367083 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (613 / 400 : ℝ) (13113198857 / 12500000000 : ℝ)
    (46297367083 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1225_denomUpper :
    Real.exp (141619359346383219 / 10000000000000000 : ℝ) ≤ (14140039722313151 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (141619359346383219 / 10000000000000000 : ℝ)
    (1556688016411 / 1000000000000 : ℝ) (14140039722313151 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1225_denomLower :
    (1388103844102021 / 1000000000 : ℝ) ≤ Real.exp (17679311541121373 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (17679311541121373 / 1250000000000000 : ℝ) (311157792557
    / 200000000000 : ℝ) (1388103844102021 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1225_product_lower :
    (18158217791121373 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (49 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1225_leftExp
    (by norm_num : (0 : ℝ) ≤ (46239531527 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1225_product_upper :
    Real.pi * Real.exp (613 / 400 : ℝ) ≤ (145447484346383219 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1225_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1225_endpointLower :
    (1338267 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (49 / 64 : ℝ) (613 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (18158217791121373 / 1250000000000000 : ℝ) (Real.pi * Real.exp (49 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell1225_product_lower
  have hD : Real.exp (Real.pi * Real.exp (613 / 400 : ℝ) - (49 / 128 : ℝ)) ≤
      (14140039722313151 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1225_denomUpper
    linarith [hpThetaJensenCell1225_product_upper]
  have hi : (1 / (14140039722313151 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (613 / 400 : ℝ) - (49 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (14140039722313151 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (14140039722313151 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((49 / 128 : ℝ) - Real.pi * Real.exp (613 / 400 : ℝ)) := by
    rw [show (49 / 128 : ℝ) - Real.pi * Real.exp (613 / 400 : ℝ) =
      -(Real.pi * Real.exp (613 / 400 : ℝ) - (49 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (49 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (49 / 32 : ℝ)) := by
    have h := hpThetaJensenCell1225_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (14140039722313151 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1225_endpointUpper :
    hpThetaJensenKernelEndpointUpper (49 / 64 : ℝ) (613 / 800 : ℝ) ≤ (438543 / 400000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (613 / 400 : ℝ)) (145447484346383219 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (613 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1225_product_upper
  have hD : (1388103844102021 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (49 / 32 : ℝ) - (613 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1225_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1225_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (49 / 32 : ℝ) - (613 / 1600 : ℝ)) ≤
      (1 / (1388103844102021 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1388103844102021 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((613 / 1600 : ℝ) - Real.pi * Real.exp (49 / 32 : ℝ)) ≤
      (2 / (1388103844102021 / 1000000000 : ℝ) : ℝ) := by
    rw [show (613 / 1600 : ℝ) - Real.pi * Real.exp (49 / 32 : ℝ) =
      -(Real.pi * Real.exp (49 / 32 : ℝ) - (613 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (145447484346383219 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (145447484346383219 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1225_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (49 / 64 : ℝ) (613 / 800 : ℝ)) :
    (1338267 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (438543 / 400000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1225_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1225_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1226_leftExp :
    (46297367081 / 10000000000 : ℝ) ≤ Real.exp (613 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (613 / 400 : ℝ) (1049055908559 / 1000000000000 : ℝ)
    (46297367081 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1226_rightExp :
    Real.exp (1227 / 800 : ℝ) ≤ (46355274977 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1227 / 800 : ℝ) (1049096888107 / 1000000000000 : ℝ)
    (46355274977 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1226_denomUpper :
    Real.exp (141798157380818361 / 10000000000000000 : ℝ) ≤ (2879026916038107 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (141798157380818361 / 10000000000000000 : ℝ)
    (778779024659 / 500000000000 : ℝ) (2879026916038107 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1226_denomLower :
    (7065569762865023 / 5000000000 : ℝ) ≤ Real.exp (17701632880341619 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (17701632880341619 / 1250000000000000 : ℝ) (1556657387397
    / 1000000000000 : ℝ) (7065569762865023 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1226_product_lower :
    (18180929755341619 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (613 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1226_leftExp
    (by norm_num : (0 : ℝ) ≤ (46297367081 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1226_product_upper :
    Real.pi * Real.exp (1227 / 800 : ℝ) ≤ (145629407380818361 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1226_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1226_endpointLower :
    (5272127 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (613 / 800 : ℝ) (1227 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (18180929755341619 / 1250000000000000 : ℝ) (Real.pi * Real.exp (613 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1226_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1227 / 800 : ℝ) - (613 / 1600 : ℝ)) ≤
      (2879026916038107 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1226_denomUpper
    linarith [hpThetaJensenCell1226_product_upper]
  have hi : (1 / (2879026916038107 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1227 / 800 : ℝ) - (613 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2879026916038107 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2879026916038107 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((613 / 1600 : ℝ) - Real.pi * Real.exp (1227 / 800 : ℝ)) := by
    rw [show (613 / 1600 : ℝ) - Real.pi * Real.exp (1227 / 800 : ℝ) =
      -(Real.pi * Real.exp (1227 / 800 : ℝ) - (613 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (613 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (613 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1226_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2879026916038107 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1226_endpointUpper :
    hpThetaJensenKernelEndpointUpper (613 / 800 : ℝ) (1227 / 1600 : ℝ) ≤ (2699511 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1227 / 800 : ℝ)) (145629407380818361 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1227 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1226_product_upper
  have hD : (7065569762865023 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (613 / 400 : ℝ) - (1227 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1226_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1226_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (613 / 400 : ℝ) - (1227 / 3200 : ℝ)) ≤
      (1 / (7065569762865023 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (7065569762865023 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1227 / 3200 : ℝ) - Real.pi * Real.exp (613 / 400 : ℝ)) ≤
      (2 / (7065569762865023 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1227 / 3200 : ℝ) - Real.pi * Real.exp (613 / 400 : ℝ) =
      -(Real.pi * Real.exp (613 / 400 : ℝ) - (1227 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (145629407380818361 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (145629407380818361 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1226_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (613 / 800 : ℝ) (1227 / 1600 : ℝ)) :
    (5272127 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2699511 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1226_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1226_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1227_leftExp :
    (1854210999 / 400000000 : ℝ) ≤ Real.exp (1227 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1227 / 800 : ℝ) (524548444053 / 500000000000 : ℝ)
    (1854210999 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1227_rightExp :
    Real.exp (307 / 200 : ℝ) ≤ (464132553 / 100000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (307 / 200 : ℝ) (524568934627 / 500000000000 : ℝ)
    (464132553 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1227_denomUpper :
    Real.exp (1419771829576929 / 100000000000000 : ℝ) ≤ (7327582483585113 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1419771829576929 / 100000000000000 : ℝ) (9740185479 /
    6250000000 : ℝ) (7327582483585113 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1227_denomLower :
    (7193036867749531 / 5000000000 : ℝ) ≤ Real.exp (708959305096301 / 50000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (708959305096301 / 50000000000000 : ℝ) (194690925363 /
    125000000000 : ℝ) (7193036867749531 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1227_product_lower :
    (728146805096301 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (1227 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1227_leftExp
    (by norm_num : (0 : ℝ) ≤ (1854210999 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1227_product_upper :
    Real.pi * Real.exp (307 / 200 : ℝ) ≤ (1458115579576929 / 100000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1227_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1227_endpointLower :
    (5192291 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1227 / 1600 : ℝ) (307 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (728146805096301 / 50000000000000 : ℝ) (Real.pi * Real.exp (1227 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1227_product_lower
  have hD : Real.exp (Real.pi * Real.exp (307 / 200 : ℝ) - (1227 / 3200 : ℝ)) ≤
      (7327582483585113 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1227_denomUpper
    linarith [hpThetaJensenCell1227_product_upper]
  have hi : (1 / (7327582483585113 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (307 / 200 : ℝ) - (1227 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7327582483585113 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7327582483585113 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1227 / 3200 : ℝ) - Real.pi * Real.exp (307 / 200 : ℝ)) := by
    rw [show (1227 / 3200 : ℝ) - Real.pi * Real.exp (307 / 200 : ℝ) =
      -(Real.pi * Real.exp (307 / 200 : ℝ) - (1227 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1227 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1227 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1227_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7327582483585113 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1227_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1227 / 1600 : ℝ) (307 / 400 : ℝ) ≤ (664673 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (307 / 200 : ℝ)) (1458115579576929 / 100000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (307 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1227_product_upper
  have hD : (7193036867749531 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1227 / 800 : ℝ) - (307 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1227_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1227_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1227 / 800 : ℝ) - (307 / 800 : ℝ)) ≤
      (1 / (7193036867749531 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (7193036867749531 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((307 / 800 : ℝ) - Real.pi * Real.exp (1227 / 800 : ℝ)) ≤
      (2 / (7193036867749531 / 5000000000 : ℝ) : ℝ) := by
    rw [show (307 / 800 : ℝ) - Real.pi * Real.exp (1227 / 800 : ℝ) =
      -(Real.pi * Real.exp (1227 / 800 : ℝ) - (307 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1458115579576929 / 100000000000000 : ℝ) ^ 2 - 6 *
      (1458115579576929 / 100000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1227_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1227 / 1600 : ℝ) (307 / 400 : ℝ)) :
    (5192291 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (664673 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1227_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1227_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1228_leftExp :
    (23206627649 / 5000000000 : ℝ) ≤ Real.exp (307 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (307 / 200 : ℝ) (1049137869253 / 1000000000000 : ℝ)
    (23206627649 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1228_rightExp :
    Real.exp (1229 / 800 : ℝ) ≤ (23235654073 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1229 / 800 : ℝ) (1049178852003 / 1000000000000 : ℝ)
    (23235654073 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1228_denomUpper :
    Real.exp (71078218186158289 / 5000000000000000 : ℝ) ≤ (233128631532397 / 156250000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (71078218186158289 / 5000000000000000 : ℝ) (779651450973
    / 500000000000 : ℝ) (233128631532397 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1228_denomLower :
    (585837614575559 / 400000000 : ℝ) ≤ Real.exp (8873180408634651 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8873180408634651 / 625000000000000 : ℝ) (1558399012793 /
    1000000000000 : ℝ) (585837614575559 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1228_product_lower :
    (9113219471134651 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (307 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1228_leftExp
    (by norm_num : (0 : ℝ) ≤ (23206627649 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1228_product_upper :
    Real.pi * Real.exp (1229 / 800 : ℝ) ≤ (72996968186158289 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1228_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1228_endpointLower :
    (2556773 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (307 / 400 : ℝ) (1229 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9113219471134651 / 625000000000000 : ℝ) (Real.pi * Real.exp (307 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1228_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1229 / 800 : ℝ) - (307 / 800 : ℝ)) ≤
      (233128631532397 / 156250000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1228_denomUpper
    linarith [hpThetaJensenCell1228_product_upper]
  have hi : (1 / (233128631532397 / 156250000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1229 / 800 : ℝ) - (307 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (233128631532397 / 156250000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (233128631532397 / 156250000 : ℝ) : ℝ) ≤
      2 * Real.exp ((307 / 800 : ℝ) - Real.pi * Real.exp (1229 / 800 : ℝ)) := by
    rw [show (307 / 800 : ℝ) - Real.pi * Real.exp (1229 / 800 : ℝ) =
      -(Real.pi * Real.exp (1229 / 800 : ℝ) - (307 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (307 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (307 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1228_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (233128631532397 / 156250000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1228_endpointUpper :
    hpThetaJensenKernelEndpointUpper (307 / 400 : ℝ) (1229 / 1600 : ℝ) ≤ (10473721 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1229 / 800 : ℝ)) (72996968186158289 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1229 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1228_product_upper
  have hD : (585837614575559 / 400000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (307 / 200 : ℝ) - (1229 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1228_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1228_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (307 / 200 : ℝ) - (1229 / 3200 : ℝ)) ≤
      (1 / (585837614575559 / 400000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (585837614575559 / 400000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1229 / 3200 : ℝ) - Real.pi * Real.exp (307 / 200 : ℝ)) ≤
      (2 / (585837614575559 / 400000000 : ℝ) : ℝ) := by
    rw [show (1229 / 3200 : ℝ) - Real.pi * Real.exp (307 / 200 : ℝ) =
      -(Real.pi * Real.exp (307 / 200 : ℝ) - (1229 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (72996968186158289 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (72996968186158289 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1228_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (307 / 400 : ℝ) (1229 / 1600 : ℝ)) :
    (2556773 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (10473721 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1228_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1228_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1229_leftExp :
    (46471308143 / 10000000000 : ℝ) ≤ Real.exp (1229 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1229 / 800 : ℝ) (524589426001 / 500000000000 : ℝ)
    (46471308143 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1229_rightExp :
    Real.exp (123 / 80 : ℝ) ≤ (46529433601 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (123 / 80 : ℝ) (16394059943 / 15625000000 : ℝ)
    (46529433601 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1229_denomUpper :
    Real.exp (142335917894866393 / 10000000000000000 : ℝ) ≤ (7595220318411121 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (142335917894866393 / 10000000000000000 : ℝ)
    (780088864347 / 500000000000 : ℝ) (7595220318411121 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1229_denomLower :
    (14910840879247271 / 10000000000 : ℝ) ≤ Real.exp (17768767486447957 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (17768767486447957 / 1250000000000000 : ℝ) (77963611031 /
    50000000000 : ℝ) (14910840879247271 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1229_product_lower :
    (18249236236447957 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1229 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1229_leftExp
    (by norm_num : (0 : ℝ) ≤ (46471308143 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1229_product_upper :
    Real.pi * Real.exp (123 / 80 : ℝ) ≤ (146176542894866393 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1229_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1229_endpointLower :
    (10071759 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1229 / 1600 : ℝ) (123 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (18249236236447957 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1229 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1229_product_lower
  have hD : Real.exp (Real.pi * Real.exp (123 / 80 : ℝ) - (1229 / 3200 : ℝ)) ≤
      (7595220318411121 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1229_denomUpper
    linarith [hpThetaJensenCell1229_product_upper]
  have hi : (1 / (7595220318411121 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (123 / 80 : ℝ) - (1229 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7595220318411121 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7595220318411121 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1229 / 3200 : ℝ) - Real.pi * Real.exp (123 / 80 : ℝ)) := by
    rw [show (1229 / 3200 : ℝ) - Real.pi * Real.exp (123 / 80 : ℝ) =
      -(Real.pi * Real.exp (123 / 80 : ℝ) - (1229 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1229 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1229 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1229_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7595220318411121 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1229_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1229 / 1600 : ℝ) (123 / 160 : ℝ) ≤ (82519 / 80000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (123 / 80 : ℝ)) (146176542894866393 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (123 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1229_product_upper
  have hD : (14910840879247271 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1229 / 800 : ℝ) - (123 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell1229_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1229_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1229 / 800 : ℝ) - (123 / 320 : ℝ)) ≤
      (1 / (14910840879247271 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (14910840879247271 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((123 / 320 : ℝ) - Real.pi * Real.exp (1229 / 800 : ℝ)) ≤
      (2 / (14910840879247271 / 10000000000 : ℝ) : ℝ) := by
    rw [show (123 / 320 : ℝ) - Real.pi * Real.exp (1229 / 800 : ℝ) =
      -(Real.pi * Real.exp (1229 / 800 : ℝ) - (123 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (146176542894866393 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (146176542894866393 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1229_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1229 / 1600 : ℝ) (123 / 160 : ℝ)) :
    (10071759 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (82519 / 80000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1229_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1229_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1230_leftExp :
    (46529433599 / 10000000000 : ℝ) ≤ Real.exp (123 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (123 / 80 : ℝ) (1049219836351 / 1000000000000 : ℝ)
    (46529433599 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1230_rightExp :
    Real.exp (1231 / 800 : ℝ) ≤ (46587631759 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1231 / 800 : ℝ) (524630411151 / 500000000000 : ℝ)
    (46587631759 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1230_denomUpper :
    Real.exp (142515627820652087 / 10000000000000000 : ℝ) ≤ (15465895618992829 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (142515627820652087 / 10000000000000000 : ℝ)
    (1561054160469 / 1000000000000 : ℝ) (15465895618992829 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1230_denomLower :
    (15180878931812591 / 10000000000 : ℝ) ≤ Real.exp (17791202669893701 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (17791202669893701 / 1250000000000000 : ℝ) (780073514943
    / 500000000000 : ℝ) (15180878931812591 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1230_product_lower :
    (18272062044893701 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (123 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1230_leftExp
    (by norm_num : (0 : ℝ) ≤ (46529433599 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1230_product_upper :
    Real.pi * Real.exp (1231 / 800 : ℝ) ≤ (146359377820652087 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1230_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1230_endpointLower :
    (2479639 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (123 / 160 : ℝ) (1231 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (18272062044893701 / 1250000000000000 : ℝ) (Real.pi * Real.exp (123 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell1230_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1231 / 800 : ℝ) - (123 / 320 : ℝ)) ≤
      (15465895618992829 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1230_denomUpper
    linarith [hpThetaJensenCell1230_product_upper]
  have hi : (1 / (15465895618992829 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1231 / 800 : ℝ) - (123 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (15465895618992829 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (15465895618992829 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((123 / 320 : ℝ) - Real.pi * Real.exp (1231 / 800 : ℝ)) := by
    rw [show (123 / 320 : ℝ) - Real.pi * Real.exp (1231 / 800 : ℝ) =
      -(Real.pi * Real.exp (1231 / 800 : ℝ) - (123 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (123 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (123 / 80 : ℝ)) := by
    have h := hpThetaJensenCell1230_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (15465895618992829 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1230_endpointUpper :
    hpThetaJensenKernelEndpointUpper (123 / 160 : ℝ) (1231 / 1600 : ℝ) ≤ (2031641 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1231 / 800 : ℝ)) (146359377820652087 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1231 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1230_product_upper
  have hD : (15180878931812591 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (123 / 80 : ℝ) - (1231 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1230_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1230_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (123 / 80 : ℝ) - (1231 / 3200 : ℝ)) ≤
      (1 / (15180878931812591 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (15180878931812591 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1231 / 3200 : ℝ) - Real.pi * Real.exp (123 / 80 : ℝ)) ≤
      (2 / (15180878931812591 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1231 / 3200 : ℝ) - Real.pi * Real.exp (123 / 80 : ℝ) =
      -(Real.pi * Real.exp (123 / 80 : ℝ) - (1231 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (146359377820652087 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (146359377820652087 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1230_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (123 / 160 : ℝ) (1231 / 1600 : ℝ)) :
    (2479639 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2031641 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1230_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1230_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1231_leftExp :
    (46587631757 / 10000000000 : ℝ) ≤ Real.exp (1231 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1231 / 800 : ℝ) (1049260822301 / 1000000000000 : ℝ)
    (46587631757 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1231_rightExp :
    Real.exp (77 / 50 : ℝ) ≤ (46645902711 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (77 / 50 : ℝ) (524650904927 / 500000000000 : ℝ)
    (46645902711 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1231_denomUpper :
    Real.exp (142695566435558623 / 10000000000000000 : ℝ) ≤ (629868226172107 / 400000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (142695566435558623 / 10000000000000000 : ℝ)
    (1561932200821 / 1000000000000 : ℝ) (629868226172107 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1231_denomLower :
    (7728080218700793 / 5000000000 : ℝ) ≤ Real.exp (17813666403342143 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (17813666403342143 / 1250000000000000 : ℝ) (390255861033
    / 250000000000 : ℝ) (7728080218700793 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1231_product_lower :
    (18294916403342143 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1231 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1231_leftExp
    (by norm_num : (0 : ℝ) ≤ (46587631757 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1231_product_upper :
    Real.pi * Real.exp (77 / 50 : ℝ) ≤ (146542441435558623 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1231_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1231_endpointLower :
    (9767459 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1231 / 1600 : ℝ) (77 / 100 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (18294916403342143 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1231 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1231_product_lower
  have hD : Real.exp (Real.pi * Real.exp (77 / 50 : ℝ) - (1231 / 3200 : ℝ)) ≤
      (629868226172107 / 400000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1231_denomUpper
    linarith [hpThetaJensenCell1231_product_upper]
  have hi : (1 / (629868226172107 / 400000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (77 / 50 : ℝ) - (1231 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (629868226172107 / 400000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (629868226172107 / 400000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1231 / 3200 : ℝ) - Real.pi * Real.exp (77 / 50 : ℝ)) := by
    rw [show (1231 / 3200 : ℝ) - Real.pi * Real.exp (77 / 50 : ℝ) =
      -(Real.pi * Real.exp (77 / 50 : ℝ) - (1231 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1231 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1231 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1231_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (629868226172107 / 400000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1231_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1231 / 1600 : ℝ) (77 / 100 : ℝ) ≤ (10003683 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (77 / 50 : ℝ)) (146542441435558623 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (77 / 100 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1231_product_upper
  have hD : (7728080218700793 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1231 / 800 : ℝ) - (77 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1231_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1231_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1231 / 800 : ℝ) - (77 / 200 : ℝ)) ≤
      (1 / (7728080218700793 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (7728080218700793 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((77 / 200 : ℝ) - Real.pi * Real.exp (1231 / 800 : ℝ)) ≤
      (2 / (7728080218700793 / 5000000000 : ℝ) : ℝ) := by
    rw [show (77 / 200 : ℝ) - Real.pi * Real.exp (1231 / 800 : ℝ) =
      -(Real.pi * Real.exp (1231 / 800 : ℝ) - (77 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (146542441435558623 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (146542441435558623 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1231_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1231 / 1600 : ℝ) (77 / 100 : ℝ)) :
    (9767459 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (10003683 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1231_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1231_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1232_leftExp :
    (46645902709 / 10000000000 : ℝ) ≤ Real.exp (77 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (77 / 50 : ℝ) (1049301809853 / 1000000000000 : ℝ)
    (46645902709 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1232_rightExp :
    Real.exp (1233 / 800 : ℝ) ≤ (23352123273 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1233 / 800 : ℝ) (524671399503 / 500000000000 : ℝ)
    (23352123273 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1232_denomUpper :
    Real.exp (71437867009593889 / 5000000000000000 : ℝ) ≤ (16032981381785887 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (71437867009593889 / 5000000000000000 : ℝ) (390702963319
    / 250000000000 : ℝ) (16032981381785887 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1232_denomLower :
    (3147358724417331 / 2000000000 : ℝ) ≤ Real.exp (17836158722921591 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (17836158722921591 / 1250000000000000 : ℝ) (1561901466923
    / 1000000000000 : ℝ) (3147358724417331 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1232_product_lower :
    (18317799347921591 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (77 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1232_leftExp
    (by norm_num : (0 : ℝ) ≤ (46645902709 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1232_product_upper :
    Real.pi * Real.exp (1233 / 800 : ℝ) ≤ (73362867009593889 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1232_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1232_endpointLower :
    (9618441 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (77 / 100 : ℝ) (1233 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (18317799347921591 / 1250000000000000 : ℝ) (Real.pi * Real.exp (77 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell1232_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1233 / 800 : ℝ) - (77 / 200 : ℝ)) ≤
      (16032981381785887 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1232_denomUpper
    linarith [hpThetaJensenCell1232_product_upper]
  have hi : (1 / (16032981381785887 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1233 / 800 : ℝ) - (77 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (16032981381785887 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (16032981381785887 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((77 / 200 : ℝ) - Real.pi * Real.exp (1233 / 800 : ℝ)) := by
    rw [show (77 / 200 : ℝ) - Real.pi * Real.exp (1233 / 800 : ℝ) =
      -(Real.pi * Real.exp (1233 / 800 : ℝ) - (77 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (77 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (77 / 50 : ℝ)) := by
    have h := hpThetaJensenCell1232_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (16032981381785887 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1232_endpointUpper :
    hpThetaJensenKernelEndpointUpper (77 / 100 : ℝ) (1233 / 1600 : ℝ) ≤ (1970257 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1233 / 800 : ℝ)) (73362867009593889 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1233 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1232_product_upper
  have hD : (3147358724417331 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (77 / 50 : ℝ) - (1233 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1232_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1232_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (77 / 50 : ℝ) - (1233 / 3200 : ℝ)) ≤
      (1 / (3147358724417331 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3147358724417331 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1233 / 3200 : ℝ) - Real.pi * Real.exp (77 / 50 : ℝ)) ≤
      (2 / (3147358724417331 / 2000000000 : ℝ) : ℝ) := by
    rw [show (1233 / 3200 : ℝ) - Real.pi * Real.exp (77 / 50 : ℝ) =
      -(Real.pi * Real.exp (77 / 50 : ℝ) - (1233 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (73362867009593889 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (73362867009593889 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1232_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (77 / 100 : ℝ) (1233 / 1600 : ℝ)) :
    (9618441 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1970257 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1232_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1232_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1233_leftExp :
    (2919015409 / 625000000 : ℝ) ≤ Real.exp (1233 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1233 / 800 : ℝ) (209868559801 / 200000000000 : ℝ)
    (2919015409 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1233_rightExp :
    Real.exp (617 / 400 : ℝ) ≤ (23381331679 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (617 / 400 : ℝ) (3279324343 / 3125000000 : ℝ)
    (23381331679 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1233_denomUpper :
    Real.exp (71528065433424647 / 5000000000000000 : ℝ) ≤ (1632483587861473 / 1000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (71528065433424647 / 5000000000000000 : ℝ) (1563693121443
    / 1000000000000 : ℝ) (1632483587861473 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1233_denomLower :
    (8011444527429329 / 5000000000 : ℝ) ≤ Real.exp (1116167478973891 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1116167478973891 / 78125000000000 : ℝ) (195347637723 /
    125000000000 : ℝ) (8011444527429329 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1233_product_lower :
    (1146294432098891 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (1233 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1233_leftExp
    (by norm_num : (0 : ℝ) ≤ (2919015409 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1233_product_upper :
    Real.pi * Real.exp (617 / 400 : ℝ) ≤ (73454627933424647 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1233_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1233_endpointLower :
    (4735739 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1233 / 1600 : ℝ) (617 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1146294432098891 / 78125000000000 : ℝ) (Real.pi * Real.exp (1233 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1233_product_lower
  have hD : Real.exp (Real.pi * Real.exp (617 / 400 : ℝ) - (1233 / 3200 : ℝ)) ≤
      (1632483587861473 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1233_denomUpper
    linarith [hpThetaJensenCell1233_product_upper]
  have hi : (1 / (1632483587861473 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (617 / 400 : ℝ) - (1233 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1632483587861473 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1632483587861473 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1233 / 3200 : ℝ) - Real.pi * Real.exp (617 / 400 : ℝ)) := by
    rw [show (1233 / 3200 : ℝ) - Real.pi * Real.exp (617 / 400 : ℝ) =
      -(Real.pi * Real.exp (617 / 400 : ℝ) - (1233 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1233 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1233 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1233_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1632483587861473 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1233_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1233 / 1600 : ℝ) (617 / 800 : ℝ) ≤ (1940197 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (617 / 400 : ℝ)) (73454627933424647 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (617 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1233_product_upper
  have hD : (8011444527429329 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1233 / 800 : ℝ) - (617 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1233_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1233_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1233 / 800 : ℝ) - (617 / 1600 : ℝ)) ≤
      (1 / (8011444527429329 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (8011444527429329 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((617 / 1600 : ℝ) - Real.pi * Real.exp (1233 / 800 : ℝ)) ≤
      (2 / (8011444527429329 / 5000000000 : ℝ) : ℝ) := by
    rw [show (617 / 1600 : ℝ) - Real.pi * Real.exp (1233 / 800 : ℝ) =
      -(Real.pi * Real.exp (1233 / 800 : ℝ) - (617 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (73454627933424647 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (73454627933424647 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1233_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1233 / 1600 : ℝ) (617 / 800 : ℝ)) :
    (4735739 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1940197 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1233_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1233_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1234_leftExp :
    (9352532671 / 2000000000 : ℝ) ≤ Real.exp (617 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (617 / 400 : ℝ) (1049383789759 / 1000000000000 : ℝ)
    (9352532671 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1234_rightExp :
    Real.exp (247 / 160 : ℝ) ≤ (11705288309 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (247 / 160 : ℝ) (209884956423 / 200000000000 : ℝ)
    (11705288309 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1234_denomUpper :
    Real.exp (35809189314536237 / 2500000000000000 : ℝ) ≤ (16622384666232903 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (35809189314536237 / 2500000000000000 : ℝ) (1564576008863
    / 1000000000000 : ℝ) (16622384666232903 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1234_denomLower :
    (16314559736614063 / 10000000000 : ℝ) ≤ Real.exp (3576245852369029 / 250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (3576245852369029 / 250000000000000 : ℝ) (1563662352309 /
    1000000000000 : ℝ) (16314559736614063 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1234_product_lower :
    (3672730227369029 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (617 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1234_leftExp
    (by norm_num : (0 : ℝ) ≤ (9352532671 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1234_product_upper :
    Real.pi * Real.exp (247 / 160 : ℝ) ≤ (36773251814536237 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1234_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1234_endpointLower :
    (1865309 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (617 / 800 : ℝ) (247 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3672730227369029 / 250000000000000 : ℝ) (Real.pi * Real.exp (617 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1234_product_lower
  have hD : Real.exp (Real.pi * Real.exp (247 / 160 : ℝ) - (617 / 1600 : ℝ)) ≤
      (16622384666232903 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1234_denomUpper
    linarith [hpThetaJensenCell1234_product_upper]
  have hi : (1 / (16622384666232903 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (247 / 160 : ℝ) - (617 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (16622384666232903 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (16622384666232903 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((617 / 1600 : ℝ) - Real.pi * Real.exp (247 / 160 : ℝ)) := by
    rw [show (617 / 1600 : ℝ) - Real.pi * Real.exp (247 / 160 : ℝ) =
      -(Real.pi * Real.exp (247 / 160 : ℝ) - (617 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (617 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (617 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1234_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (16622384666232903 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1234_endpointUpper :
    hpThetaJensenKernelEndpointUpper (617 / 800 : ℝ) (247 / 320 : ℝ) ≤ (9552757 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (247 / 160 : ℝ)) (36773251814536237 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (247 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1234_product_upper
  have hD : (16314559736614063 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (617 / 400 : ℝ) - (247 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1234_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1234_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (617 / 400 : ℝ) - (247 / 640 : ℝ)) ≤
      (1 / (16314559736614063 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (16314559736614063 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((247 / 640 : ℝ) - Real.pi * Real.exp (617 / 400 : ℝ)) ≤
      (2 / (16314559736614063 / 10000000000 : ℝ) : ℝ) := by
    rw [show (247 / 640 : ℝ) - Real.pi * Real.exp (617 / 400 : ℝ) =
      -(Real.pi * Real.exp (617 / 400 : ℝ) - (247 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (36773251814536237 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (36773251814536237 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1234_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (617 / 800 : ℝ) (247 / 320 : ℝ)) :
    (1865309 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (9552757 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1234_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1234_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1235_leftExp :
    (46821153233 / 10000000000 : ℝ) ≤ Real.exp (247 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (247 / 160 : ℝ) (524712391057 / 500000000000 : ℝ)
    (46821153233 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1235_rightExp :
    Real.exp (309 / 200 : ℝ) ≤ (46879716271 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (309 / 200 : ℝ) (1049465776071 / 1000000000000 : ℝ)
    (46879716271 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1235_denomUpper :
    Real.exp (143417613478959703 / 10000000000000000 : ℝ) ≤ (3385149160420559 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (143417613478959703 / 10000000000000000 : ℝ)
    (1565460519117 / 1000000000000 : ℝ) (3385149160420559 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1235_denomLower :
    (664476845063823 / 400000000 : ℝ) ≤ Real.exp (17903807553445867 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (17903807553445867 / 1250000000000000 : ℝ) (1564545222071
    / 1000000000000 : ℝ) (664476845063823 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1235_product_lower :
    (18386620053445867 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (247 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1235_leftExp
    (by norm_num : (0 : ℝ) ≤ (46821153233 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1235_product_upper :
    Real.pi * Real.exp (309 / 200 : ℝ) ≤ (147276988478959703 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1235_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1235_endpointLower :
    (71747 / 78125000 : ℝ) ≤ hpThetaTraceEndpointLower (247 / 320 : ℝ) (309 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (18386620053445867 / 1250000000000000 : ℝ) (Real.pi * Real.exp (247 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1235_product_lower
  have hD : Real.exp (Real.pi * Real.exp (309 / 200 : ℝ) - (247 / 640 : ℝ)) ≤
      (3385149160420559 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1235_denomUpper
    linarith [hpThetaJensenCell1235_product_upper]
  have hi : (1 / (3385149160420559 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (309 / 200 : ℝ) - (247 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3385149160420559 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3385149160420559 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((247 / 640 : ℝ) - Real.pi * Real.exp (309 / 200 : ℝ)) := by
    rw [show (247 / 640 : ℝ) - Real.pi * Real.exp (309 / 200 : ℝ) =
      -(Real.pi * Real.exp (309 / 200 : ℝ) - (247 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (247 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (247 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1235_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3385149160420559 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1235_endpointUpper :
    hpThetaJensenKernelEndpointUpper (247 / 320 : ℝ) (309 / 400 : ℝ) ≤ (587911 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (309 / 200 : ℝ)) (147276988478959703 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (309 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1235_product_upper
  have hD : (664476845063823 / 400000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (247 / 160 : ℝ) - (309 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1235_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1235_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (247 / 160 : ℝ) - (309 / 800 : ℝ)) ≤
      (1 / (664476845063823 / 400000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (664476845063823 / 400000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((309 / 800 : ℝ) - Real.pi * Real.exp (247 / 160 : ℝ)) ≤
      (2 / (664476845063823 / 400000000 : ℝ) : ℝ) := by
    rw [show (309 / 800 : ℝ) - Real.pi * Real.exp (247 / 160 : ℝ) =
      -(Real.pi * Real.exp (247 / 160 : ℝ) - (309 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (147276988478959703 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (147276988478959703 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1235_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (247 / 320 : ℝ) (309 / 400 : ℝ)) :
    (71747 / 78125000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (587911 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1235_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1235_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1236_leftExp :
    (46879716269 / 10000000000 : ℝ) ≤ Real.exp (309 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (309 / 200 : ℝ) (104946577607 / 100000000000 : ℝ)
    (46879716269 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1236_rightExp :
    Real.exp (1237 / 800 : ℝ) ≤ (46938352557 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1237 / 800 : ℝ) (1049506771629 / 1000000000000 : ℝ)
    (46938352557 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1236_denomUpper :
    Real.exp (143598699824603301 / 10000000000000000 : ℝ) ≤ (4308759985711781 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (143598699824603301 / 10000000000000000 : ℝ)
    (783173327919 / 500000000000 : ℝ) (4308759985711781 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1236_denomLower :
    (338301824142469 / 200000000 : ℝ) ≤ Real.exp (17926414574120031 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (17926414574120031 / 1250000000000000 : ℝ) (195678714331
    / 125000000000 : ℝ) (338301824142469 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1236_product_lower :
    (18409617699120031 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (309 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1236_leftExp
    (by norm_num : (0 : ℝ) ≤ (46879716269 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1236_product_upper :
    Real.pi * Real.exp (1237 / 800 : ℝ) ≤ (147461199824603301 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1236_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1236_endpointLower :
    (2260667 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (309 / 400 : ℝ) (1237 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (18409617699120031 / 1250000000000000 : ℝ) (Real.pi * Real.exp (309 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1236_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1237 / 800 : ℝ) - (309 / 800 : ℝ)) ≤
      (4308759985711781 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1236_denomUpper
    linarith [hpThetaJensenCell1236_product_upper]
  have hi : (1 / (4308759985711781 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1237 / 800 : ℝ) - (309 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4308759985711781 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4308759985711781 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((309 / 800 : ℝ) - Real.pi * Real.exp (1237 / 800 : ℝ)) := by
    rw [show (309 / 800 : ℝ) - Real.pi * Real.exp (1237 / 800 : ℝ) =
      -(Real.pi * Real.exp (1237 / 800 : ℝ) - (309 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (309 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (309 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1236_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4308759985711781 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1236_endpointUpper :
    hpThetaJensenKernelEndpointUpper (309 / 400 : ℝ) (1237 / 1600 : ℝ) ≤ (9262417 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1237 / 800 : ℝ)) (147461199824603301 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1237 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1236_product_upper
  have hD : (338301824142469 / 200000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (309 / 200 : ℝ) - (1237 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1236_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1236_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (309 / 200 : ℝ) - (1237 / 3200 : ℝ)) ≤
      (1 / (338301824142469 / 200000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (338301824142469 / 200000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1237 / 3200 : ℝ) - Real.pi * Real.exp (309 / 200 : ℝ)) ≤
      (2 / (338301824142469 / 200000000 : ℝ) : ℝ) := by
    rw [show (1237 / 3200 : ℝ) - Real.pi * Real.exp (309 / 200 : ℝ) =
      -(Real.pi * Real.exp (309 / 200 : ℝ) - (1237 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (147461199824603301 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (147461199824603301 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1236_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (309 / 400 : ℝ) (1237 / 1600 : ℝ)) :
    (2260667 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (9262417 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1236_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1236_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1237_leftExp :
    (9387670511 / 2000000000 : ℝ) ≤ Real.exp (1237 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1237 / 800 : ℝ) (262376692907 / 250000000000 : ℝ)
    (9387670511 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1237_rightExp :
    Real.exp (619 / 400 : ℝ) ≤ (5874632773 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (619 / 400 : ℝ) (262386942197 / 250000000000 : ℝ)
    (5874632773 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1237_denomUpper :
    Real.exp (17972502072227389 / 1250000000000000 : ℝ) ≤ (17550390367358509 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (17972502072227389 / 1250000000000000 : ℝ) (783617211303
    / 500000000000 : ℝ) (17550390367358509 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1237_denomLower :
    (1076511909323853 / 625000000 : ℝ) ≤ Real.exp (3589810071999189 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3589810071999189 / 250000000000000 : ℝ) (313263166729 /
    200000000000 : ℝ) (1076511909323853 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1237_product_lower :
    (3686528821999189 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1237 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1237_leftExp
    (by norm_num : (0 : ℝ) ≤ (9387670511 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1237_product_upper :
    Real.pi * Real.exp (619 / 400 : ℝ) ≤ (18455705197227389 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1237_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1237_endpointLower :
    (2225919 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (1237 / 1600 : ℝ) (619 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3686528821999189 / 250000000000000 : ℝ) (Real.pi * Real.exp (1237 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1237_product_lower
  have hD : Real.exp (Real.pi * Real.exp (619 / 400 : ℝ) - (1237 / 3200 : ℝ)) ≤
      (17550390367358509 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1237_denomUpper
    linarith [hpThetaJensenCell1237_product_upper]
  have hi : (1 / (17550390367358509 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (619 / 400 : ℝ) - (1237 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (17550390367358509 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (17550390367358509 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1237 / 3200 : ℝ) - Real.pi * Real.exp (619 / 400 : ℝ)) := by
    rw [show (1237 / 3200 : ℝ) - Real.pi * Real.exp (619 / 400 : ℝ) =
      -(Real.pi * Real.exp (619 / 400 : ℝ) - (1237 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1237 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1237 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1237_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (17550390367358509 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1237_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1237 / 1600 : ℝ) (619 / 800 : ℝ) ≤ (17813 / 19531250 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (619 / 400 : ℝ)) (18455705197227389 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (619 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1237_product_upper
  have hD : (1076511909323853 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1237 / 800 : ℝ) - (619 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1237_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1237_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1237 / 800 : ℝ) - (619 / 1600 : ℝ)) ≤
      (1 / (1076511909323853 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1076511909323853 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((619 / 1600 : ℝ) - Real.pi * Real.exp (1237 / 800 : ℝ)) ≤
      (2 / (1076511909323853 / 625000000 : ℝ) : ℝ) := by
    rw [show (619 / 1600 : ℝ) - Real.pi * Real.exp (1237 / 800 : ℝ) =
      -(Real.pi * Real.exp (1237 / 800 : ℝ) - (619 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (18455705197227389 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (18455705197227389 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1237_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1237 / 1600 : ℝ) (619 / 800 : ℝ)) :
    (2225919 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17813 / 19531250 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1237_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1237_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1238_leftExp :
    (46997062181 / 10000000000 : ℝ) ≤ Real.exp (619 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (619 / 400 : ℝ) (1049547768787 / 1000000000000 : ℝ)
    (46997062181 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1238_rightExp :
    Real.exp (1239 / 800 : ℝ) ≤ (47055845243 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1239 / 800 : ℝ) (262397191887 / 250000000000 : ℝ)
    (47055845243 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1238_denomUpper :
    Real.exp (143961564024492099 / 10000000000000000 : ℝ) ≤ (17871923064148211 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (143961564024492099 / 10000000000000000 : ℝ)
    (784061911513 / 500000000000 : ℝ) (17871923064148211 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1238_denomLower :
    (3507868470742073 / 2000000000 : ℝ) ≤ Real.exp (17971714946416519 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (17971714946416519 / 1250000000000000 : ℝ) (783601791321
    / 500000000000 : ℝ) (3507868470742073 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1238_product_lower :
    (18455699321416519 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (619 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1238_leftExp
    (by norm_num : (0 : ℝ) ≤ (46997062181 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1238_product_upper :
    Real.pi * Real.exp (1239 / 800 : ℝ) ≤ (147830314024492099 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1238_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1238_endpointLower :
    (1095827 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (619 / 800 : ℝ) (1239 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (18455699321416519 / 1250000000000000 : ℝ) (Real.pi * Real.exp (619 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1238_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1239 / 800 : ℝ) - (619 / 1600 : ℝ)) ≤
      (17871923064148211 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1238_denomUpper
    linarith [hpThetaJensenCell1238_product_upper]
  have hi : (1 / (17871923064148211 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1239 / 800 : ℝ) - (619 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (17871923064148211 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (17871923064148211 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((619 / 1600 : ℝ) - Real.pi * Real.exp (1239 / 800 : ℝ)) := by
    rw [show (619 / 1600 : ℝ) - Real.pi * Real.exp (1239 / 800 : ℝ) =
      -(Real.pi * Real.exp (1239 / 800 : ℝ) - (619 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (619 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (619 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1238_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (17871923064148211 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1238_endpointUpper :
    hpThetaJensenKernelEndpointUpper (619 / 800 : ℝ) (1239 / 1600 : ℝ) ≤ (2245017 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1239 / 800 : ℝ)) (147830314024492099 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1239 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1238_product_upper
  have hD : (3507868470742073 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (619 / 400 : ℝ) - (1239 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1238_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1238_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (619 / 400 : ℝ) - (1239 / 3200 : ℝ)) ≤
      (1 / (3507868470742073 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3507868470742073 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1239 / 3200 : ℝ) - Real.pi * Real.exp (619 / 400 : ℝ)) ≤
      (2 / (3507868470742073 / 2000000000 : ℝ) : ℝ) := by
    rw [show (1239 / 3200 : ℝ) - Real.pi * Real.exp (619 / 400 : ℝ) =
      -(Real.pi * Real.exp (619 / 400 : ℝ) - (1239 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (147830314024492099 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (147830314024492099 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1238_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (619 / 800 : ℝ) (1239 / 1600 : ℝ)) :
    (1095827 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2245017 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1238_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1238_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1239_leftExp :
    (1176396131 / 250000000 : ℝ) ≤ Real.exp (1239 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1239 / 800 : ℝ) (1049588767547 / 1000000000000 : ℝ)
    (1176396131 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1239_rightExp :
    Real.exp (31 / 20 : ℝ) ≤ (47114701827 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (31 / 20 : ℝ) (104962976791 / 100000000000 : ℝ)
    (47114701827 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1239_denomUpper :
    Real.exp (144143342456790411 / 10000000000000000 : ℝ) ≤ (4549941699552587 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (144143342456790411 / 10000000000000000 : ℝ)
    (1569014860739 / 1000000000000 : ℝ) (4549941699552587 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1239_denomLower :
    (8930336269878501 / 5000000000 : ℝ) ≤ Real.exp (449860209247569 / 31250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (449860209247569 / 31250000000000 : ℝ) (196011620659 /
    125000000000 : ℝ) (8930336269878501 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1239_product_lower :
    (461969584247569 / 31250000000000 : ℝ) ≤ Real.pi * Real.exp (1239 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1239_leftExp
    (by norm_num : (0 : ℝ) ≤ (1176396131 / 250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1239_product_upper :
    Real.pi * Real.exp (31 / 20 : ℝ) ≤ (148015217456790411 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1239_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1239_endpointLower :
    (4315733 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1239 / 1600 : ℝ) (31 / 40 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (461969584247569 / 31250000000000 : ℝ) (Real.pi * Real.exp (1239 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1239_product_lower
  have hD : Real.exp (Real.pi * Real.exp (31 / 20 : ℝ) - (1239 / 3200 : ℝ)) ≤
      (4549941699552587 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1239_denomUpper
    linarith [hpThetaJensenCell1239_product_upper]
  have hi : (1 / (4549941699552587 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (31 / 20 : ℝ) - (1239 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4549941699552587 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4549941699552587 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1239 / 3200 : ℝ) - Real.pi * Real.exp (31 / 20 : ℝ)) := by
    rw [show (1239 / 3200 : ℝ) - Real.pi * Real.exp (31 / 20 : ℝ) =
      -(Real.pi * Real.exp (31 / 20 : ℝ) - (1239 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1239 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1239 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1239_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4549941699552587 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1239_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1239 / 1600 : ℝ) (31 / 40 : ℝ) ≤ (8841829 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (31 / 20 : ℝ)) (148015217456790411 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (31 / 40 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1239_product_upper
  have hD : (8930336269878501 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1239 / 800 : ℝ) - (31 / 80 : ℝ)) := by
    apply le_trans hpThetaJensenCell1239_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1239_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1239 / 800 : ℝ) - (31 / 80 : ℝ)) ≤
      (1 / (8930336269878501 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (8930336269878501 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((31 / 80 : ℝ) - Real.pi * Real.exp (1239 / 800 : ℝ)) ≤
      (2 / (8930336269878501 / 5000000000 : ℝ) : ℝ) := by
    rw [show (31 / 80 : ℝ) - Real.pi * Real.exp (1239 / 800 : ℝ) =
      -(Real.pi * Real.exp (1239 / 800 : ℝ) - (31 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (148015217456790411 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (148015217456790411 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1239_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1239 / 1600 : ℝ) (31 / 40 : ℝ)) :
    (4315733 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8841829 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1239_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1239_endpointUpper

def hpThetaJensenCellsBatch061Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (180463 / 156250000 : ℝ)
  | 1 => (11376297 / 10000000000 : ℝ)
  | 2 => (11205307 / 10000000000 : ℝ)
  | 3 => (2207327 / 2000000000 : ℝ)
  | 4 => (5435127 / 5000000000 : ℝ)
  | 5 => (1338267 / 1250000000 : ℝ)
  | 6 => (5272127 / 5000000000 : ℝ)
  | 7 => (5192291 / 5000000000 : ℝ)
  | 8 => (2556773 / 2500000000 : ℝ)
  | 9 => (10071759 / 10000000000 : ℝ)
  | 10 => (2479639 / 2500000000 : ℝ)
  | 11 => (9767459 / 10000000000 : ℝ)
  | 12 => (9618441 / 10000000000 : ℝ)
  | 13 => (4735739 / 5000000000 : ℝ)
  | 14 => (1865309 / 2000000000 : ℝ)
  | 15 => (71747 / 78125000 : ℝ)
  | 16 => (2260667 / 2500000000 : ℝ)
  | 17 => (2225919 / 2500000000 : ℝ)
  | 18 => (1095827 / 1250000000 : ℝ)
  | 19 => (4315733 / 5000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch061Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (5913013 / 5000000000 : ℝ)
  | 1 => (11648803 / 10000000000 : ℝ)
  | 2 => (458959 / 400000000 : ℝ)
  | 3 => (11301513 / 10000000000 : ℝ)
  | 4 => (11131389 / 10000000000 : ℝ)
  | 5 => (438543 / 400000000 : ℝ)
  | 6 => (2699511 / 2500000000 : ℝ)
  | 7 => (664673 / 625000000 : ℝ)
  | 8 => (10473721 / 10000000000 : ℝ)
  | 9 => (82519 / 80000000 : ℝ)
  | 10 => (2031641 / 2000000000 : ℝ)
  | 11 => (10003683 / 10000000000 : ℝ)
  | 12 => (1970257 / 2000000000 : ℝ)
  | 13 => (1940197 / 2000000000 : ℝ)
  | 14 => (9552757 / 10000000000 : ℝ)
  | 15 => (587911 / 625000000 : ℝ)
  | 16 => (9262417 / 10000000000 : ℝ)
  | 17 => (17813 / 19531250 : ℝ)
  | 18 => (2245017 / 2500000000 : ℝ)
  | 19 => (8841829 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch061_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1220 : ℝ) + (j.val : ℝ)) / 1600)
      (((1220 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch061Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch061Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1220_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1221_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1222_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1223_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1224_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1225_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1226_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1227_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1228_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1229_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1230_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1231_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1232_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1233_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1234_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1235_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1236_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1237_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1238_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1239_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper] at h ⊢
    exact h

end HodgeProofHP
