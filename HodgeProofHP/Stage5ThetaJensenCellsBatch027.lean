import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell540_leftExp :
    (19640329759 / 10000000000 : ℝ) ≤ Real.exp (27 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (27 / 40 : ℝ) (255329448923 / 250000000000 : ℝ)
    (19640329759 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell540_rightExp :
    Real.exp (541 / 800 : ℝ) ≤ (19664895523 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (541 / 800 : ℝ) (1021357691699 / 1000000000000 : ℝ)
    (19664895523 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell540_denomUpper :
    Real.exp (60091598120788139 / 10000000000000000 : ℝ) ≤ (508926376873 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (60091598120788139 / 10000000000000000 : ℝ) (9426371681 /
    7812500000 : ℝ) (508926376873 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell540_denomLower :
    (4038840310159 / 10000000000 : ℝ) ≤ Real.exp (7501409731029541 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7501409731029541 / 1250000000000000 : ℝ) (48250910467 /
    40000000000 : ℝ) (4038840310159 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell540_product_lower :
    (7712737856029541 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (27 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell540_leftExp
    (by norm_num : (0 : ℝ) ≤ (19640329759 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell540_product_upper :
    Real.pi * Real.exp (541 / 800 : ℝ) ≤ (61779098120788139 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell540_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell540_endpointLower :
    (5662108319 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (27 / 80 : ℝ) (541 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7712737856029541 / 1250000000000000 : ℝ) (Real.pi * Real.exp (27 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell540_product_lower
  have hD : Real.exp (Real.pi * Real.exp (541 / 800 : ℝ) - (27 / 160 : ℝ)) ≤
      (508926376873 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell540_denomUpper
    linarith [hpThetaJensenCell540_product_upper]
  have hi : (1 / (508926376873 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (541 / 800 : ℝ) - (27 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (508926376873 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (508926376873 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((27 / 160 : ℝ) - Real.pi * Real.exp (541 / 800 : ℝ)) := by
    rw [show (27 / 160 : ℝ) - Real.pi * Real.exp (541 / 800 : ℝ) =
      -(Real.pi * Real.exp (541 / 800 : ℝ) - (27 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (27 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (27 / 40 : ℝ)) := by
    have h := hpThetaJensenCell540_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (508926376873 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell540_endpointUpper :
    hpThetaJensenKernelEndpointUpper (27 / 80 : ℝ) (541 / 1600 : ℝ) ≤ (5739432291 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (541 / 800 : ℝ)) (61779098120788139 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (541 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell540_product_upper
  have hD : (4038840310159 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (27 / 40 : ℝ) - (541 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell540_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell540_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (27 / 40 : ℝ) - (541 / 3200 : ℝ)) ≤
      (1 / (4038840310159 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4038840310159 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((541 / 3200 : ℝ) - Real.pi * Real.exp (27 / 40 : ℝ)) ≤
      (2 / (4038840310159 / 10000000000 : ℝ) : ℝ) := by
    rw [show (541 / 3200 : ℝ) - Real.pi * Real.exp (27 / 40 : ℝ) =
      -(Real.pi * Real.exp (27 / 40 : ℝ) - (541 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (61779098120788139 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (61779098120788139 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell540_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (27 / 80 : ℝ) (541 / 1600 : ℝ)) :
    (5662108319 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5739432291 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell540_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell540_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell541_leftExp :
    (9832447761 / 5000000000 : ℝ) ≤ Real.exp (541 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (541 / 800 : ℝ) (510678845849 / 500000000000 : ℝ)
    (9832447761 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell541_rightExp :
    Real.exp (271 / 400 : ℝ) ≤ (4922373003 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (271 / 400 : ℝ) (1021397589263 / 1000000000000 : ℝ)
    (4922373003 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell541_denomUpper :
    Real.exp (15041436319613779 / 2500000000000000 : ℝ) ≤ (51271394583 / 125000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (15041436319613779 / 2500000000000000 : ℝ) (301713795757
    / 250000000000 : ℝ) (51271394583 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell541_denomLower :
    (2034429587679 / 5000000000 : ℝ) ≤ Real.exp (3755333028296939 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3755333028296939 / 625000000000000 : ℝ) (120655193531 /
    100000000000 : ℝ) (2034429587679 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell541_product_lower :
    (3861192403296939 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (541 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell541_leftExp
    (by norm_num : (0 : ℝ) ≤ (9832447761 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell541_product_upper :
    Real.pi * Real.exp (271 / 400 : ℝ) ≤ (15464092569613779 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell541_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell541_endpointLower :
    (352288101 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (541 / 1600 : ℝ) (271 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3861192403296939 / 625000000000000 : ℝ) (Real.pi * Real.exp (541 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell541_product_lower
  have hD : Real.exp (Real.pi * Real.exp (271 / 400 : ℝ) - (541 / 3200 : ℝ)) ≤
      (51271394583 / 125000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell541_denomUpper
    linarith [hpThetaJensenCell541_product_upper]
  have hi : (1 / (51271394583 / 125000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (271 / 400 : ℝ) - (541 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (51271394583 / 125000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (51271394583 / 125000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((541 / 3200 : ℝ) - Real.pi * Real.exp (271 / 400 : ℝ)) := by
    rw [show (541 / 3200 : ℝ) - Real.pi * Real.exp (271 / 400 : ℝ) =
      -(Real.pi * Real.exp (271 / 400 : ℝ) - (541 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (541 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (541 / 800 : ℝ)) := by
    have h := hpThetaJensenCell541_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (51271394583 / 125000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell541_endpointUpper :
    hpThetaJensenKernelEndpointUpper (541 / 1600 : ℝ) (271 / 800 : ℝ) ≤ (5713636753 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (271 / 400 : ℝ)) (15464092569613779 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (271 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell541_product_upper
  have hD : (2034429587679 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (541 / 800 : ℝ) - (271 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell541_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell541_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (541 / 800 : ℝ) - (271 / 1600 : ℝ)) ≤
      (1 / (2034429587679 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2034429587679 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((271 / 1600 : ℝ) - Real.pi * Real.exp (541 / 800 : ℝ)) ≤
      (2 / (2034429587679 / 5000000000 : ℝ) : ℝ) := by
    rw [show (271 / 1600 : ℝ) - Real.pi * Real.exp (541 / 800 : ℝ) =
      -(Real.pi * Real.exp (541 / 800 : ℝ) - (271 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (15464092569613779 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (15464092569613779 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell541_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (541 / 1600 : ℝ) (271 / 800 : ℝ)) :
    (352288101 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5713636753 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell541_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell541_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell542_leftExp :
    (19689492011 / 10000000000 : ℝ) ≤ Real.exp (271 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (271 / 400 : ℝ) (510698794631 / 500000000000 : ℝ)
    (19689492011 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell542_rightExp :
    Real.exp (543 / 800 : ℝ) ≤ (9857059633 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (543 / 800 : ℝ) (510718744193 / 500000000000 : ℝ)
    (9857059633 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell542_denomUpper :
    Real.exp (30119994543615369 / 5000000000000000 : ℝ) ≤ (4132277561877 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (30119994543615369 / 5000000000000000 : ℝ) (1207135220279
    / 1000000000000 : ℝ) (4132277561877 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell542_denomLower :
    (4099140725443 / 10000000000 : ℝ) ≤ Real.exp (7519934448227689 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7519934448227689 / 1250000000000000 : ℝ) (1206831537599
    / 1000000000000 : ℝ) (4099140725443 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell542_product_lower :
    (7732043823227689 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (271 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell542_leftExp
    (by norm_num : (0 : ℝ) ≤ (19689492011 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell542_product_upper :
    Real.pi * Real.exp (543 / 800 : ℝ) ≤ (30966869543615369 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell542_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell542_endpointLower :
    (5611167799 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (271 / 800 : ℝ) (543 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7732043823227689 / 1250000000000000 : ℝ) (Real.pi * Real.exp (271 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell542_product_lower
  have hD : Real.exp (Real.pi * Real.exp (543 / 800 : ℝ) - (271 / 1600 : ℝ)) ≤
      (4132277561877 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell542_denomUpper
    linarith [hpThetaJensenCell542_product_upper]
  have hi : (1 / (4132277561877 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (543 / 800 : ℝ) - (271 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4132277561877 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4132277561877 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((271 / 1600 : ℝ) - Real.pi * Real.exp (543 / 800 : ℝ)) := by
    rw [show (271 / 1600 : ℝ) - Real.pi * Real.exp (543 / 800 : ℝ) =
      -(Real.pi * Real.exp (543 / 800 : ℝ) - (271 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (271 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (271 / 400 : ℝ)) := by
    have h := hpThetaJensenCell542_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4132277561877 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell542_endpointUpper :
    hpThetaJensenKernelEndpointUpper (271 / 800 : ℝ) (543 / 1600 : ℝ) ≤ (5687898491 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (543 / 800 : ℝ)) (30966869543615369 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (543 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell542_product_upper
  have hD : (4099140725443 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (271 / 400 : ℝ) - (543 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell542_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell542_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (271 / 400 : ℝ) - (543 / 3200 : ℝ)) ≤
      (1 / (4099140725443 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4099140725443 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((543 / 3200 : ℝ) - Real.pi * Real.exp (271 / 400 : ℝ)) ≤
      (2 / (4099140725443 / 10000000000 : ℝ) : ℝ) := by
    rw [show (543 / 3200 : ℝ) - Real.pi * Real.exp (271 / 400 : ℝ) =
      -(Real.pi * Real.exp (271 / 400 : ℝ) - (543 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (30966869543615369 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (30966869543615369 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell542_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (271 / 800 : ℝ) (543 / 1600 : ℝ)) :
    (5611167799 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5687898491 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell542_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell542_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell543_leftExp :
    (3942823853 / 2000000000 : ℝ) ≤ Real.exp (543 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (543 / 800 : ℝ) (204287497677 / 200000000000 : ℝ)
    (3942823853 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell543_rightExp :
    Real.exp (17 / 25 : ℝ) ≤ (19738777323 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (17 / 25 : ℝ) (1021477389067 / 1000000000000 : ℝ)
    (19738777323 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell543_denomUpper :
    Real.exp (60314329666495539 / 10000000000000000 : ℝ) ≤ (1040777905431 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (60314329666495539 / 10000000000000000 : ℝ) (603707843821
    / 500000000000 : ℝ) (1040777905431 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell543_denomLower :
    (1032421888159 / 2500000000 : ℝ) ≤ Real.exp (1505842984249247 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1505842984249247 / 250000000000000 : ℝ) (1207111569271 /
    1000000000000 : ℝ) (1032421888159 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell543_product_lower :
    (1548342984249247 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (543 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell543_leftExp
    (by norm_num : (0 : ℝ) ≤ (3942823853 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell543_product_upper :
    Real.pi * Real.exp (17 / 25 : ℝ) ≤ (62011204666495539 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell543_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell543_endpointLower :
    (2792891537 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (543 / 1600 : ℝ) (17 / 50 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1548342984249247 / 250000000000000 : ℝ) (Real.pi * Real.exp (543 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell543_product_lower
  have hD : Real.exp (Real.pi * Real.exp (17 / 25 : ℝ) - (543 / 3200 : ℝ)) ≤
      (1040777905431 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell543_denomUpper
    linarith [hpThetaJensenCell543_product_upper]
  have hi : (1 / (1040777905431 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (17 / 25 : ℝ) - (543 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1040777905431 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1040777905431 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((543 / 3200 : ℝ) - Real.pi * Real.exp (17 / 25 : ℝ)) := by
    rw [show (543 / 3200 : ℝ) - Real.pi * Real.exp (17 / 25 : ℝ) =
      -(Real.pi * Real.exp (17 / 25 : ℝ) - (543 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (543 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (543 / 800 : ℝ)) := by
    have h := hpThetaJensenCell543_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1040777905431 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell543_endpointUpper :
    hpThetaJensenKernelEndpointUpper (543 / 1600 : ℝ) (17 / 50 : ℝ) ≤ (1132443543 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (17 / 25 : ℝ)) (62011204666495539 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (17 / 50 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell543_product_upper
  have hD : (1032421888159 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (543 / 800 : ℝ) - (17 / 100 : ℝ)) := by
    apply le_trans hpThetaJensenCell543_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell543_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (543 / 800 : ℝ) - (17 / 100 : ℝ)) ≤
      (1 / (1032421888159 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1032421888159 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((17 / 100 : ℝ) - Real.pi * Real.exp (543 / 800 : ℝ)) ≤
      (2 / (1032421888159 / 2500000000 : ℝ) : ℝ) := by
    rw [show (17 / 100 : ℝ) - Real.pi * Real.exp (543 / 800 : ℝ) =
      -(Real.pi * Real.exp (543 / 800 : ℝ) - (17 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (62011204666495539 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (62011204666495539 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell543_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (543 / 1600 : ℝ) (17 / 50 : ℝ)) :
    (2792891537 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1132443543 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell543_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell543_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell544_leftExp :
    (9869388661 / 5000000000 : ℝ) ≤ Real.exp (17 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (17 / 25 : ℝ) (510738694533 / 500000000000 : ℝ)
    (9869388661 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell544_rightExp :
    Real.exp (109 / 160 : ℝ) ≤ (9881733111 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (109 / 160 : ℝ) (1021517291307 / 1000000000000 : ℝ)
    (9881733111 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell544_denomUpper :
    Real.exp (30194383569385823 / 5000000000000000 : ℝ) ≤ (4194216396801 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (30194383569385823 / 5000000000000000 : ℝ) (1207696585849
    / 1000000000000 : ℝ) (4194216396801 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell544_denomLower :
    (832100455243 / 2000000000 : ℝ) ≤ Real.exp (3769253745286039 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3769253745286039 / 625000000000000 : ℝ) (603696015523 /
    500000000000 : ℝ) (832100455243 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell544_product_lower :
    (3875699057786039 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (17 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell544_leftExp
    (by norm_num : (0 : ℝ) ≤ (9869388661 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell544_product_upper :
    Real.pi * Real.exp (109 / 160 : ℝ) ≤ (31044383569385823 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell544_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell544_endpointLower :
    (173764239 / 312500000 : ℝ) ≤ hpThetaTraceEndpointLower (17 / 50 : ℝ) (109 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3875699057786039 / 625000000000000 : ℝ) (Real.pi * Real.exp (17 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell544_product_lower
  have hD : Real.exp (Real.pi * Real.exp (109 / 160 : ℝ) - (17 / 100 : ℝ)) ≤
      (4194216396801 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell544_denomUpper
    linarith [hpThetaJensenCell544_product_upper]
  have hi : (1 / (4194216396801 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (109 / 160 : ℝ) - (17 / 100 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4194216396801 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4194216396801 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((17 / 100 : ℝ) - Real.pi * Real.exp (109 / 160 : ℝ)) := by
    rw [show (17 / 100 : ℝ) - Real.pi * Real.exp (109 / 160 : ℝ) =
      -(Real.pi * Real.exp (109 / 160 : ℝ) - (17 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (17 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (17 / 25 : ℝ)) := by
    have h := hpThetaJensenCell544_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4194216396801 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell544_endpointUpper :
    hpThetaJensenKernelEndpointUpper (17 / 50 : ℝ) (109 / 320 : ℝ) ≤ (2818297317 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (109 / 160 : ℝ)) (31044383569385823 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (109 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell544_product_upper
  have hD : (832100455243 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (17 / 25 : ℝ) - (109 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell544_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell544_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (17 / 25 : ℝ) - (109 / 640 : ℝ)) ≤
      (1 / (832100455243 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (832100455243 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((109 / 640 : ℝ) - Real.pi * Real.exp (17 / 25 : ℝ)) ≤
      (2 / (832100455243 / 2000000000 : ℝ) : ℝ) := by
    rw [show (109 / 640 : ℝ) - Real.pi * Real.exp (17 / 25 : ℝ) =
      -(Real.pi * Real.exp (17 / 25 : ℝ) - (109 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (31044383569385823 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (31044383569385823 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell544_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (17 / 50 : ℝ) (109 / 320 : ℝ)) :
    (173764239 / 312500000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2818297317 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell544_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell544_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell545_leftExp :
    (19763466221 / 10000000000 : ℝ) ≤ Real.exp (109 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (109 / 160 : ℝ) (510758645653 / 500000000000 : ℝ)
    (19763466221 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell545_rightExp :
    Real.exp (273 / 400 : ℝ) ≤ (19788186001 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (273 / 400 : ℝ) (204311439021 / 200000000000 : ℝ)
    (19788186001 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell545_denomUpper :
    Real.exp (60463301623439593 / 10000000000000000 : ℝ) ≤ (1056398641279 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (60463301623439593 / 10000000000000000 : ℝ) (60398895781
    / 50000000000 : ℝ) (1056398641279 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell545_denomLower :
    (838317509027 / 2000000000 : ℝ) ≤ Real.exp (7547812171520479 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7547812171520479 / 1250000000000000 : ℝ) (150959115457 /
    125000000000 : ℝ) (838317509027 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell545_product_lower :
    (7761093421520479 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (109 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell545_leftExp
    (by norm_num : (0 : ℝ) ≤ (19763466221 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell545_product_upper :
    Real.pi * Real.exp (273 / 400 : ℝ) ≤ (62166426623439593 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell545_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell545_endpointLower :
    (221407429 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (109 / 320 : ℝ) (273 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7761093421520479 / 1250000000000000 : ℝ) (Real.pi * Real.exp (109 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell545_product_lower
  have hD : Real.exp (Real.pi * Real.exp (273 / 400 : ℝ) - (109 / 640 : ℝ)) ≤
      (1056398641279 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell545_denomUpper
    linarith [hpThetaJensenCell545_product_upper]
  have hi : (1 / (1056398641279 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (273 / 400 : ℝ) - (109 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1056398641279 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1056398641279 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((109 / 640 : ℝ) - Real.pi * Real.exp (273 / 400 : ℝ)) := by
    rw [show (109 / 640 : ℝ) - Real.pi * Real.exp (273 / 400 : ℝ) =
      -(Real.pi * Real.exp (273 / 400 : ℝ) - (109 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (109 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (109 / 160 : ℝ)) := by
    have h := hpThetaJensenCell545_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1056398641279 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell545_endpointUpper :
    hpThetaJensenKernelEndpointUpper (109 / 320 : ℝ) (273 / 800 : ℝ) ≤ (1122205891 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (273 / 400 : ℝ)) (62166426623439593 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (273 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell545_product_upper
  have hD : (838317509027 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (109 / 160 : ℝ) - (273 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell545_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell545_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (109 / 160 : ℝ) - (273 / 1600 : ℝ)) ≤
      (1 / (838317509027 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (838317509027 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((273 / 1600 : ℝ) - Real.pi * Real.exp (109 / 160 : ℝ)) ≤
      (2 / (838317509027 / 2000000000 : ℝ) : ℝ) := by
    rw [show (273 / 1600 : ℝ) - Real.pi * Real.exp (109 / 160 : ℝ) =
      -(Real.pi * Real.exp (109 / 160 : ℝ) - (273 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (62166426623439593 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (62166426623439593 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell545_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (109 / 320 : ℝ) (273 / 800 : ℝ)) :
    (221407429 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1122205891 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell545_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell545_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell546_leftExp :
    (9894093 / 5000000 : ℝ) ≤ Real.exp (273 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (273 / 400 : ℝ) (31923662347 / 31250000000 : ℝ) (9894093
    / 5000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell546_rightExp :
    Real.exp (547 / 800 : ℝ) ≤ (198129367 / 100000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (547 / 800 : ℝ) (1021597100463 / 1000000000000 : ℝ)
    (198129367 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell546_denomUpper :
    Real.exp (605379332461631 / 100000000000000 : ℝ) ≤ (425724883653 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (605379332461631 / 100000000000000 : ℝ) (12082596777 /
    10000000000 : ℝ) (425724883653 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell546_denomLower :
    (4222946035727 / 10000000000 : ℝ) ≤ Real.exp (3778564489507 / 625000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3778564489507 / 625000000000 : ℝ) (1207954247821 /
    1000000000000 : ℝ) (4222946035727 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell546_product_lower :
    (3885400427007 / 625000000000 : ℝ) ≤ Real.pi * Real.exp (273 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell546_leftExp
    (by norm_num : (0 : ℝ) ≤ (9894093 / 5000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell546_product_upper :
    Real.pi * Real.exp (547 / 800 : ℝ) ≤ (622441832461631 / 100000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell546_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell546_endpointLower :
    (5509973503 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (273 / 800 : ℝ) (547 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3885400427007 / 625000000000 : ℝ) (Real.pi * Real.exp (273 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell546_product_lower
  have hD : Real.exp (Real.pi * Real.exp (547 / 800 : ℝ) - (273 / 1600 : ℝ)) ≤
      (425724883653 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell546_denomUpper
    linarith [hpThetaJensenCell546_product_upper]
  have hi : (1 / (425724883653 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (547 / 800 : ℝ) - (273 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (425724883653 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (425724883653 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((273 / 1600 : ℝ) - Real.pi * Real.exp (547 / 800 : ℝ)) := by
    rw [show (273 / 1600 : ℝ) - Real.pi * Real.exp (547 / 800 : ℝ) =
      -(Real.pi * Real.exp (547 / 800 : ℝ) - (273 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (273 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (273 / 400 : ℝ)) := by
    have h := hpThetaJensenCell546_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (425724883653 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell546_endpointUpper :
    hpThetaJensenKernelEndpointUpper (273 / 800 : ℝ) (547 / 1600 : ℝ) ≤ (1117104477 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (547 / 800 : ℝ)) (622441832461631 / 100000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (547 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell546_product_upper
  have hD : (4222946035727 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (273 / 400 : ℝ) - (547 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell546_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell546_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (273 / 400 : ℝ) - (547 / 3200 : ℝ)) ≤
      (1 / (4222946035727 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4222946035727 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((547 / 3200 : ℝ) - Real.pi * Real.exp (273 / 400 : ℝ)) ≤
      (2 / (4222946035727 / 10000000000 : ℝ) : ℝ) := by
    rw [show (547 / 3200 : ℝ) - Real.pi * Real.exp (273 / 400 : ℝ) =
      -(Real.pi * Real.exp (273 / 400 : ℝ) - (547 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (622441832461631 / 100000000000000 : ℝ) ^ 2 - 6 *
      (622441832461631 / 100000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell546_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (273 / 800 : ℝ) (547 / 1600 : ℝ)) :
    (5509973503 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1117104477 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell546_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell546_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell547_leftExp :
    (19812936699 / 10000000000 : ℝ) ≤ Real.exp (547 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (547 / 800 : ℝ) (510798550231 / 500000000000 : ℝ)
    (19812936699 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell547_rightExp :
    Real.exp (137 / 200 : ℝ) ≤ (4959429589 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (137 / 200 : ℝ) (1021637007379 / 1000000000000 : ℝ)
    (4959429589 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell547_denomUpper :
    Real.exp (15153165530795277 / 2500000000000000 : ℝ) ≤ (1072295486679 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (15153165530795277 / 2500000000000000 : ℝ) (604270936401
    / 500000000000 : ℝ) (1072295486679 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell547_denomLower :
    (4254580456373 / 10000000000 : ℝ) ≤ Real.exp (7566457928760601 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7566457928760601 / 1250000000000000 : ℝ) (18878687567 /
    15625000000 : ℝ) (4254580456373 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell547_product_lower :
    (7780520428760601 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (547 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell547_leftExp
    (by norm_num : (0 : ℝ) ≤ (19812936699 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell547_product_upper :
    Real.pi * Real.exp (137 / 200 : ℝ) ≤ (15580509280795277 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell547_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell547_endpointLower :
    (2742409593 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (547 / 1600 : ℝ) (137 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7780520428760601 / 1250000000000000 : ℝ) (Real.pi * Real.exp (547 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell547_product_lower
  have hD : Real.exp (Real.pi * Real.exp (137 / 200 : ℝ) - (547 / 3200 : ℝ)) ≤
      (1072295486679 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell547_denomUpper
    linarith [hpThetaJensenCell547_product_upper]
  have hi : (1 / (1072295486679 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (137 / 200 : ℝ) - (547 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1072295486679 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1072295486679 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((547 / 3200 : ℝ) - Real.pi * Real.exp (137 / 200 : ℝ)) := by
    rw [show (547 / 3200 : ℝ) - Real.pi * Real.exp (137 / 200 : ℝ) =
      -(Real.pi * Real.exp (137 / 200 : ℝ) - (547 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (547 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (547 / 800 : ℝ)) := by
    have h := hpThetaJensenCell547_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1072295486679 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell547_endpointUpper :
    hpThetaJensenKernelEndpointUpper (547 / 1600 : ℝ) (137 / 400 : ℝ) ≤ (2780036811 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (137 / 200 : ℝ)) (15580509280795277 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (137 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell547_product_upper
  have hD : (4254580456373 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (547 / 800 : ℝ) - (137 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell547_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell547_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (547 / 800 : ℝ) - (137 / 800 : ℝ)) ≤
      (1 / (4254580456373 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4254580456373 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((137 / 800 : ℝ) - Real.pi * Real.exp (547 / 800 : ℝ)) ≤
      (2 / (4254580456373 / 10000000000 : ℝ) : ℝ) := by
    rw [show (137 / 800 : ℝ) - Real.pi * Real.exp (547 / 800 : ℝ) =
      -(Real.pi * Real.exp (547 / 800 : ℝ) - (137 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (15580509280795277 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (15580509280795277 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell547_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (547 / 1600 : ℝ) (137 / 400 : ℝ)) :
    (2742409593 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2780036811 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell547_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell547_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell548_leftExp :
    (3967543671 / 2000000000 : ℝ) ≤ Real.exp (137 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (137 / 200 : ℝ) (510818503689 / 500000000000 : ℝ)
    (3967543671 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell548_rightExp :
    Real.exp (549 / 800 : ℝ) ≤ (19862531009 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (549 / 800 : ℝ) (510838457927 / 500000000000 : ℝ)
    (19862531009 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell548_denomUpper :
    Real.exp (60687488380157337 / 10000000000000000 : ℝ) ≤ (2160698332409 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (60687488380157337 / 10000000000000000 : ℝ) (151103062709
    / 125000000000 : ℝ) (2160698332409 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell548_denomLower :
    (2143246770349 / 5000000000 : ℝ) ≤ Real.exp (1515159807058029 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1515159807058029 / 250000000000000 : ℝ) (1208518193767 /
    1000000000000 : ℝ) (2143246770349 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell548_product_lower :
    (1558050432058029 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (137 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell548_leftExp
    (by norm_num : (0 : ℝ) ≤ (3967543671 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell548_product_upper :
    Real.pi * Real.exp (549 / 800 : ℝ) ≤ (62399988380157337 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell548_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell548_endpointLower :
    (5459722969 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (137 / 400 : ℝ) (549 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1558050432058029 / 250000000000000 : ℝ) (Real.pi * Real.exp (137 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell548_product_lower
  have hD : Real.exp (Real.pi * Real.exp (549 / 800 : ℝ) - (137 / 800 : ℝ)) ≤
      (2160698332409 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell548_denomUpper
    linarith [hpThetaJensenCell548_product_upper]
  have hi : (1 / (2160698332409 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (549 / 800 : ℝ) - (137 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2160698332409 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2160698332409 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((137 / 800 : ℝ) - Real.pi * Real.exp (549 / 800 : ℝ)) := by
    rw [show (137 / 800 : ℝ) - Real.pi * Real.exp (549 / 800 : ℝ) =
      -(Real.pi * Real.exp (549 / 800 : ℝ) - (137 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (137 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (137 / 200 : ℝ)) := by
    have h := hpThetaJensenCell548_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2160698332409 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell548_endpointUpper :
    hpThetaJensenKernelEndpointUpper (137 / 400 : ℝ) (549 / 1600 : ℝ) ≤ (5534683371 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (549 / 800 : ℝ)) (62399988380157337 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (549 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell548_product_upper
  have hD : (2143246770349 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (137 / 200 : ℝ) - (549 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell548_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell548_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (137 / 200 : ℝ) - (549 / 3200 : ℝ)) ≤
      (1 / (2143246770349 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2143246770349 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((549 / 3200 : ℝ) - Real.pi * Real.exp (137 / 200 : ℝ)) ≤
      (2 / (2143246770349 / 5000000000 : ℝ) : ℝ) := by
    rw [show (549 / 3200 : ℝ) - Real.pi * Real.exp (137 / 200 : ℝ) =
      -(Real.pi * Real.exp (137 / 200 : ℝ) - (549 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (62399988380157337 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (62399988380157337 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell548_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (137 / 400 : ℝ) (549 / 1600 : ℝ)) :
    (5459722969 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5534683371 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell548_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell548_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell549_leftExp :
    (19862531007 / 10000000000 : ℝ) ≤ Real.exp (549 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (549 / 800 : ℝ) (1021676915853 / 1000000000000 : ℝ)
    (19862531007 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell549_rightExp :
    Real.exp (11 / 16 : ℝ) ≤ (19887374697 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11 / 16 : ℝ) (31928650809 / 31250000000 : ℝ)
    (19887374697 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell549_denomUpper :
    Real.exp (60762412136472321 / 10000000000000000 : ℝ) ≤ (544236973449 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (60762412136472321 / 10000000000000000 : ℝ) (604553782517
    / 500000000000 : ℝ) (544236973449 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell549_denomLower :
    (2159344027423 / 5000000000 : ℝ) ≤ Real.exp (7585152313917893 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7585152313917893 / 1250000000000000 : ℝ) (1208800816993
    / 1000000000000 : ℝ) (2159344027423 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell549_product_lower :
    (7799996063917893 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (549 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell549_leftExp
    (by norm_num : (0 : ℝ) ≤ (19862531007 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell549_product_upper :
    Real.pi * Real.exp (11 / 16 : ℝ) ≤ (62478037136472321 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell549_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell549_endpointLower :
    (679335631 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (549 / 1600 : ℝ) (11 / 32 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7799996063917893 / 1250000000000000 : ℝ) (Real.pi * Real.exp (549 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell549_product_lower
  have hD : Real.exp (Real.pi * Real.exp (11 / 16 : ℝ) - (549 / 3200 : ℝ)) ≤
      (544236973449 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell549_denomUpper
    linarith [hpThetaJensenCell549_product_upper]
  have hi : (1 / (544236973449 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (11 / 16 : ℝ) - (549 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (544236973449 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (544236973449 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((549 / 3200 : ℝ) - Real.pi * Real.exp (11 / 16 : ℝ)) := by
    rw [show (549 / 3200 : ℝ) - Real.pi * Real.exp (11 / 16 : ℝ) =
      -(Real.pi * Real.exp (11 / 16 : ℝ) - (549 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (549 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (549 / 800 : ℝ)) := by
    have h := hpThetaJensenCell549_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (544236973449 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell549_endpointUpper :
    hpThetaJensenKernelEndpointUpper (549 / 1600 : ℝ) (11 / 32 : ℝ) ≤ (688668979 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (11 / 16 : ℝ)) (62478037136472321 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (11 / 32 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell549_product_upper
  have hD : (2159344027423 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (549 / 800 : ℝ) - (11 / 64 : ℝ)) := by
    apply le_trans hpThetaJensenCell549_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell549_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (549 / 800 : ℝ) - (11 / 64 : ℝ)) ≤
      (1 / (2159344027423 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2159344027423 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((11 / 64 : ℝ) - Real.pi * Real.exp (549 / 800 : ℝ)) ≤
      (2 / (2159344027423 / 5000000000 : ℝ) : ℝ) := by
    rw [show (11 / 64 : ℝ) - Real.pi * Real.exp (549 / 800 : ℝ) =
      -(Real.pi * Real.exp (549 / 800 : ℝ) - (11 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (62478037136472321 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (62478037136472321 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell549_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (549 / 1600 : ℝ) (11 / 32 : ℝ)) :
    (679335631 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (688668979 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell549_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell549_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell550_leftExp :
    (3977474939 / 2000000000 : ℝ) ≤ Real.exp (11 / 16 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11 / 16 : ℝ) (1021716825887 / 1000000000000 : ℝ)
    (3977474939 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell550_rightExp :
    Real.exp (551 / 800 : ℝ) ≤ (19912249459 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (551 / 800 : ℝ) (1021756737481 / 1000000000000 : ℝ)
    (19912249459 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell550_denomUpper :
    Real.exp (60837433514648187 / 10000000000000000 : ℝ) ≤ (4386682143963 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (60837433514648187 / 10000000000000000 : ℝ)
    (1209391063627 / 1000000000000 : ℝ) (4386682143963 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell550_denomLower :
    (4351166796783 / 10000000000 : ℝ) ≤ Real.exp (1518903556070361 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1518903556070361 / 250000000000000 : ℝ) (302270968679 /
    250000000000 : ℝ) (4351166796783 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell550_product_lower :
    (1561950431070361 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (11 / 16 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell550_leftExp
    (by norm_num : (0 : ℝ) ≤ (3977474939 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell550_product_upper :
    Real.pi * Real.exp (551 / 800 : ℝ) ≤ (62556183514648187 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell550_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell550_endpointLower :
    (2704852809 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (11 / 32 : ℝ) (551 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1561950431070361 / 250000000000000 : ℝ) (Real.pi * Real.exp (11 / 16 : ℝ))
    (by norm_num) hpThetaJensenCell550_product_lower
  have hD : Real.exp (Real.pi * Real.exp (551 / 800 : ℝ) - (11 / 64 : ℝ)) ≤
      (4386682143963 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell550_denomUpper
    linarith [hpThetaJensenCell550_product_upper]
  have hi : (1 / (4386682143963 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (551 / 800 : ℝ) - (11 / 64 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4386682143963 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4386682143963 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((11 / 64 : ℝ) - Real.pi * Real.exp (551 / 800 : ℝ)) := by
    rw [show (11 / 64 : ℝ) - Real.pi * Real.exp (551 / 800 : ℝ) =
      -(Real.pi * Real.exp (551 / 800 : ℝ) - (11 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (11 / 16 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (11 / 16 : ℝ)) := by
    have h := hpThetaJensenCell550_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4386682143963 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell550_endpointUpper :
    hpThetaJensenKernelEndpointUpper (11 / 32 : ℝ) (551 / 1600 : ℝ) ≤ (5484079197 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (551 / 800 : ℝ)) (62556183514648187 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (551 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell550_product_upper
  have hD : (4351166796783 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (11 / 16 : ℝ) - (551 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell550_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell550_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (11 / 16 : ℝ) - (551 / 3200 : ℝ)) ≤
      (1 / (4351166796783 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4351166796783 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((551 / 3200 : ℝ) - Real.pi * Real.exp (11 / 16 : ℝ)) ≤
      (2 / (4351166796783 / 10000000000 : ℝ) : ℝ) := by
    rw [show (551 / 3200 : ℝ) - Real.pi * Real.exp (11 / 16 : ℝ) =
      -(Real.pi * Real.exp (11 / 16 : ℝ) - (551 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (62556183514648187 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (62556183514648187 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell550_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (11 / 32 : ℝ) (551 / 1600 : ℝ)) :
    (2704852809 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5484079197 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell550_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell550_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell551_leftExp :
    (19912249457 / 10000000000 : ℝ) ≤ Real.exp (551 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (551 / 800 : ℝ) (25543918437 / 25000000000 : ℝ)
    (19912249457 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell551_rightExp :
    Real.exp (69 / 100 : ℝ) ≤ (19937155333 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (69 / 100 : ℝ) (1021796650633 / 1000000000000 : ℝ)
    (19937155333 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell551_denomUpper :
    Real.exp (60912552634065469 / 10000000000000000 : ℝ) ≤ (4419758592173 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (60912552634065469 / 10000000000000000 : ℝ)
    (1209674998177 / 1000000000000 : ℝ) (4419758592173 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell551_denomLower :
    (876786518391 / 2000000000 : ℝ) ≤ Real.exp (7603895449514443 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7603895449514443 / 1250000000000000 : ℝ) (60468368383 /
    50000000000 : ℝ) (876786518391 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell551_product_lower :
    (7819520449514443 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (551 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell551_leftExp
    (by norm_num : (0 : ℝ) ≤ (19912249457 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell551_product_upper :
    Real.pi * Real.exp (69 / 100 : ℝ) ≤ (62634427634065469 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell551_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell551_endpointLower :
    (538478487 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (551 / 1600 : ℝ) (69 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7819520449514443 / 1250000000000000 : ℝ) (Real.pi * Real.exp (551 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell551_product_lower
  have hD : Real.exp (Real.pi * Real.exp (69 / 100 : ℝ) - (551 / 3200 : ℝ)) ≤
      (4419758592173 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell551_denomUpper
    linarith [hpThetaJensenCell551_product_upper]
  have hi : (1 / (4419758592173 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (69 / 100 : ℝ) - (551 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4419758592173 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4419758592173 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((551 / 3200 : ℝ) - Real.pi * Real.exp (69 / 100 : ℝ)) := by
    rw [show (551 / 3200 : ℝ) - Real.pi * Real.exp (69 / 100 : ℝ) =
      -(Real.pi * Real.exp (69 / 100 : ℝ) - (551 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (551 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (551 / 800 : ℝ)) := by
    have h := hpThetaJensenCell551_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4419758592173 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell551_endpointUpper :
    hpThetaJensenKernelEndpointUpper (551 / 1600 : ℝ) (69 / 200 : ℝ) ≤ (5458865663 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (69 / 100 : ℝ)) (62634427634065469 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (69 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell551_product_upper
  have hD : (876786518391 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (551 / 800 : ℝ) - (69 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell551_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell551_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (551 / 800 : ℝ) - (69 / 400 : ℝ)) ≤
      (1 / (876786518391 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (876786518391 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((69 / 400 : ℝ) - Real.pi * Real.exp (551 / 800 : ℝ)) ≤
      (2 / (876786518391 / 2000000000 : ℝ) : ℝ) := by
    rw [show (69 / 400 : ℝ) - Real.pi * Real.exp (551 / 800 : ℝ) =
      -(Real.pi * Real.exp (551 / 800 : ℝ) - (69 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (62634427634065469 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (62634427634065469 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell551_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (551 / 1600 : ℝ) (69 / 200 : ℝ)) :
    (538478487 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5458865663 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell551_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell551_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell552_leftExp :
    (4984288833 / 2500000000 : ℝ) ≤ Real.exp (69 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (69 / 100 : ℝ) (127724581329 / 125000000000 : ℝ)
    (4984288833 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell552_rightExp :
    Real.exp (553 / 800 : ℝ) ≤ (499052309 / 250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (553 / 800 : ℝ) (31932392667 / 31250000000 : ℝ)
    (499052309 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell552_denomUpper :
    Real.exp (1524694240588237 / 250000000000000 : ℝ) ≤ (222656401287 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1524694240588237 / 250000000000000 : ℝ) (241991873889 /
    200000000000 : ℝ) (222656401287 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell552_denomLower :
    (552123537291 / 1250000000 : ℝ) ≤ Real.exp (1903321334180267 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1903321334180267 / 312500000000000 : ℝ) (302412824141 /
    250000000000 : ℝ) (552123537291 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell552_product_lower :
    (1957325240430267 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (69 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell552_leftExp
    (by norm_num : (0 : ℝ) ≤ (4984288833 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell552_product_upper :
    Real.pi * Real.exp (553 / 800 : ℝ) ≤ (1567819240588237 / 250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell552_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell552_endpointLower :
    (334995187 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (69 / 200 : ℝ) (553 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1957325240430267 / 312500000000000 : ℝ) (Real.pi * Real.exp (69 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell552_product_lower
  have hD : Real.exp (Real.pi * Real.exp (553 / 800 : ℝ) - (69 / 400 : ℝ)) ≤
      (222656401287 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell552_denomUpper
    linarith [hpThetaJensenCell552_product_upper]
  have hi : (1 / (222656401287 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (553 / 800 : ℝ) - (69 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (222656401287 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (222656401287 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((69 / 400 : ℝ) - Real.pi * Real.exp (553 / 800 : ℝ)) := by
    rw [show (69 / 400 : ℝ) - Real.pi * Real.exp (553 / 800 : ℝ) =
      -(Real.pi * Real.exp (553 / 800 : ℝ) - (69 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (69 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (69 / 100 : ℝ)) := by
    have h := hpThetaJensenCell552_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (222656401287 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell552_endpointUpper :
    hpThetaJensenKernelEndpointUpper (69 / 200 : ℝ) (553 / 1600 : ℝ) ≤ (217348457 / 400000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (553 / 800 : ℝ)) (1567819240588237 / 250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (553 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell552_product_upper
  have hD : (552123537291 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (69 / 100 : ℝ) - (553 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell552_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell552_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (69 / 100 : ℝ) - (553 / 3200 : ℝ)) ≤
      (1 / (552123537291 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (552123537291 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((553 / 3200 : ℝ) - Real.pi * Real.exp (69 / 100 : ℝ)) ≤
      (2 / (552123537291 / 1250000000 : ℝ) : ℝ) := by
    rw [show (553 / 3200 : ℝ) - Real.pi * Real.exp (69 / 100 : ℝ) =
      -(Real.pi * Real.exp (69 / 100 : ℝ) - (553 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1567819240588237 / 250000000000000 : ℝ) ^ 2 - 6 *
      (1567819240588237 / 250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell552_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (69 / 200 : ℝ) (553 / 1600 : ℝ)) :
    (334995187 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (217348457 / 400000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell552_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell552_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell553_leftExp :
    (9981046179 / 5000000000 : ℝ) ≤ Real.exp (553 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (553 / 800 : ℝ) (1021836565343 / 1000000000000 : ℝ)
    (9981046179 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell553_rightExp :
    Real.exp (277 / 400 : ℝ) ≤ (19987060577 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (277 / 400 : ℝ) (204375296323 / 200000000000 : ℝ)
    (19987060577 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell553_denomUpper :
    Real.exp (61063084599279161 / 10000000000000000 : ℝ) ≤ (179471734589 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (61063084599279161 / 10000000000000000 : ℝ)
    (1210244178149 / 1000000000000 : ℝ) (179471734589 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell553_denomLower :
    (2225168401817 / 5000000000 : ℝ) ≤ Real.exp (3811343728447121 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3811343728447121 / 625000000000000 : ℝ) (241987132431 /
    200000000000 : ℝ) (2225168401817 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell553_product_lower :
    (3919546853447121 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (553 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell553_leftExp
    (by norm_num : (0 : ℝ) ≤ (9981046179 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell553_product_upper :
    Real.pi * Real.exp (277 / 400 : ℝ) ≤ (62791209599279161 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell553_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell553_endpointLower :
    (5335120173 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (553 / 1600 : ℝ) (277 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3919546853447121 / 625000000000000 : ℝ) (Real.pi * Real.exp (553 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell553_product_lower
  have hD : Real.exp (Real.pi * Real.exp (277 / 400 : ℝ) - (553 / 3200 : ℝ)) ≤
      (179471734589 / 400000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell553_denomUpper
    linarith [hpThetaJensenCell553_product_upper]
  have hi : (1 / (179471734589 / 400000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (277 / 400 : ℝ) - (553 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (179471734589 / 400000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (179471734589 / 400000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((553 / 3200 : ℝ) - Real.pi * Real.exp (277 / 400 : ℝ)) := by
    rw [show (553 / 3200 : ℝ) - Real.pi * Real.exp (277 / 400 : ℝ) =
      -(Real.pi * Real.exp (277 / 400 : ℝ) - (553 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (553 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (553 / 800 : ℝ)) := by
    have h := hpThetaJensenCell553_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (179471734589 / 400000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell553_endpointUpper :
    hpThetaJensenKernelEndpointUpper (553 / 1600 : ℝ) (277 / 800 : ℝ) ≤ (169019271 / 312500000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (277 / 400 : ℝ)) (62791209599279161 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (277 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell553_product_upper
  have hD : (2225168401817 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (553 / 800 : ℝ) - (277 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell553_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell553_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (553 / 800 : ℝ) - (277 / 1600 : ℝ)) ≤
      (1 / (2225168401817 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2225168401817 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((277 / 1600 : ℝ) - Real.pi * Real.exp (553 / 800 : ℝ)) ≤
      (2 / (2225168401817 / 5000000000 : ℝ) : ℝ) := by
    rw [show (277 / 1600 : ℝ) - Real.pi * Real.exp (553 / 800 : ℝ) =
      -(Real.pi * Real.exp (553 / 800 : ℝ) - (277 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (62791209599279161 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (62791209599279161 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell553_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (553 / 1600 : ℝ) (277 / 800 : ℝ)) :
    (5335120173 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (169019271 / 312500000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell553_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell553_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell554_leftExp :
    (624595643 / 312500000 : ℝ) ≤ Real.exp (277 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (277 / 400 : ℝ) (510938240807 / 500000000000 : ℝ)
    (624595643 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell554_rightExp :
    Real.exp (111 / 160 : ℝ) ≤ (2501507503 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (111 / 160 : ℝ) (255479099861 / 250000000000 : ℝ)
    (2501507503 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell554_denomUpper :
    Real.exp (7642312210872279 / 1250000000000000 : ℝ) ≤ (282547347827 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7642312210872279 / 1250000000000000 : ℝ) (605264712521 /
    500000000000 : ℝ) (282547347827 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell554_denomLower :
    (2241990515689 / 5000000000 : ℝ) ≤ Real.exp (238503182066707 / 39062500000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (238503182066707 / 39062500000000 : ℝ) (302555116299 /
    250000000000 : ℝ) (2241990515689 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell554_product_lower :
    (245278084410457 / 39062500000000 : ℝ) ≤ Real.pi * Real.exp (277 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell554_leftExp
    (by norm_num : (0 : ℝ) ≤ (624595643 / 312500000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell554_product_upper :
    Real.pi * Real.exp (111 / 160 : ℝ) ≤ (7858718460872279 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell554_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell554_endpointLower :
    (5310376599 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (277 / 800 : ℝ) (111 / 320 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (245278084410457 / 39062500000000 : ℝ) (Real.pi * Real.exp (277 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell554_product_lower
  have hD : Real.exp (Real.pi * Real.exp (111 / 160 : ℝ) - (277 / 1600 : ℝ)) ≤
      (282547347827 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell554_denomUpper
    linarith [hpThetaJensenCell554_product_upper]
  have hi : (1 / (282547347827 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (111 / 160 : ℝ) - (277 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (282547347827 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (282547347827 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((277 / 1600 : ℝ) - Real.pi * Real.exp (111 / 160 : ℝ)) := by
    rw [show (277 / 1600 : ℝ) - Real.pi * Real.exp (111 / 160 : ℝ) =
      -(Real.pi * Real.exp (111 / 160 : ℝ) - (277 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (277 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (277 / 400 : ℝ)) := by
    have h := hpThetaJensenCell554_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (282547347827 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell554_endpointUpper :
    hpThetaJensenKernelEndpointUpper (277 / 800 : ℝ) (111 / 320 : ℝ) ≤ (672947699 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (111 / 160 : ℝ)) (7858718460872279 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (111 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell554_product_upper
  have hD : (2241990515689 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (277 / 400 : ℝ) - (111 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell554_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell554_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (277 / 400 : ℝ) - (111 / 640 : ℝ)) ≤
      (1 / (2241990515689 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2241990515689 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((111 / 640 : ℝ) - Real.pi * Real.exp (277 / 400 : ℝ)) ≤
      (2 / (2241990515689 / 5000000000 : ℝ) : ℝ) := by
    rw [show (111 / 640 : ℝ) - Real.pi * Real.exp (277 / 400 : ℝ) =
      -(Real.pi * Real.exp (277 / 400 : ℝ) - (111 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (7858718460872279 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (7858718460872279 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell554_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (277 / 800 : ℝ) (111 / 320 : ℝ)) :
    (5310376599 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (672947699 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell554_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell554_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell555_leftExp :
    (10006030011 / 5000000000 : ℝ) ≤ Real.exp (111 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (111 / 160 : ℝ) (1021916399443 / 1000000000000 : ℝ)
    (10006030011 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell555_rightExp :
    Real.exp (139 / 200 : ℝ) ≤ (1001854537 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (139 / 200 : ℝ) (1021956318833 / 1000000000000 : ℝ)
    (1001854537 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell555_denomUpper :
    Real.exp (3060700450457441 / 500000000000000 : ℝ) ≤ (911004722833 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3060700450457441 / 500000000000000 : ℝ) (75675944429 /
    62500000000 : ℝ) (911004722833 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell555_denomLower :
    (4517923930259 / 10000000000 : ℝ) ≤ Real.exp (3820764229289689 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3820764229289689 / 625000000000000 : ℝ) (1210505706393 /
    1000000000000 : ℝ) (4517923930259 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell555_product_lower :
    (3929357979289689 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (111 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell555_leftExp
    (by norm_num : (0 : ℝ) ≤ (10006030011 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell555_product_upper :
    Real.pi * Real.exp (139 / 200 : ℝ) ≤ (3147419200457441 / 500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell555_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell555_endpointLower :
    (1321423113 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (111 / 320 : ℝ) (139 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3929357979289689 / 625000000000000 : ℝ) (Real.pi * Real.exp (111 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell555_product_lower
  have hD : Real.exp (Real.pi * Real.exp (139 / 200 : ℝ) - (111 / 640 : ℝ)) ≤
      (911004722833 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell555_denomUpper
    linarith [hpThetaJensenCell555_product_upper]
  have hi : (1 / (911004722833 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (139 / 200 : ℝ) - (111 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (911004722833 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (911004722833 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((111 / 640 : ℝ) - Real.pi * Real.exp (139 / 200 : ℝ)) := by
    rw [show (111 / 640 : ℝ) - Real.pi * Real.exp (139 / 200 : ℝ) =
      -(Real.pi * Real.exp (139 / 200 : ℝ) - (111 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (111 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (111 / 160 : ℝ)) := by
    have h := hpThetaJensenCell555_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (911004722833 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell555_endpointUpper :
    hpThetaJensenKernelEndpointUpper (111 / 320 : ℝ) (139 / 400 : ℝ) ≤ (42868851 / 80000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (139 / 200 : ℝ)) (3147419200457441 / 500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (139 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell555_product_upper
  have hD : (4517923930259 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (111 / 160 : ℝ) - (139 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell555_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell555_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (111 / 160 : ℝ) - (139 / 800 : ℝ)) ≤
      (1 / (4517923930259 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4517923930259 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((139 / 800 : ℝ) - Real.pi * Real.exp (111 / 160 : ℝ)) ≤
      (2 / (4517923930259 / 10000000000 : ℝ) : ℝ) := by
    rw [show (139 / 800 : ℝ) - Real.pi * Real.exp (111 / 160 : ℝ) =
      -(Real.pi * Real.exp (111 / 160 : ℝ) - (139 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (3147419200457441 / 500000000000000 : ℝ) ^ 2 - 6 *
      (3147419200457441 / 500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell555_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (111 / 320 : ℝ) (139 / 400 : ℝ)) :
    (1321423113 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (42868851 / 80000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell555_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell555_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell556_leftExp :
    (10018545369 / 5000000000 : ℝ) ≤ Real.exp (139 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (139 / 200 : ℝ) (63872269927 / 62500000000 : ℝ)
    (10018545369 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell556_rightExp :
    Real.exp (557 / 800 : ℝ) ≤ (5015538191 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (557 / 800 : ℝ) (510998119891 / 500000000000 : ℝ)
    (5015538191 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell556_denomUpper :
    Real.exp (15322404672078263 / 2500000000000000 : ℝ) ≤ (4589594531733 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (15322404672078263 / 2500000000000000 : ℝ) (30277530909 /
    25000000000 : ℝ) (4589594531733 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell556_denomLower :
    (910433697939 / 2000000000 : ℝ) ≤ Real.exp (3825483685360931 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3825483685360931 / 625000000000000 : ℝ) (1210791386523 /
    1000000000000 : ℝ) (910433697939 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell556_product_lower :
    (3934272747860931 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (139 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell556_leftExp
    (by norm_num : (0 : ℝ) ≤ (10018545369 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell556_product_upper :
    Real.pi * Real.exp (557 / 800 : ℝ) ≤ (15756779672078263 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell556_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell556_endpointLower :
    (2630533957 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (139 / 400 : ℝ) (557 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3934272747860931 / 625000000000000 : ℝ) (Real.pi * Real.exp (139 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell556_product_lower
  have hD : Real.exp (Real.pi * Real.exp (557 / 800 : ℝ) - (139 / 800 : ℝ)) ≤
      (4589594531733 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell556_denomUpper
    linarith [hpThetaJensenCell556_product_upper]
  have hi : (1 / (4589594531733 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (557 / 800 : ℝ) - (139 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4589594531733 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4589594531733 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((139 / 800 : ℝ) - Real.pi * Real.exp (557 / 800 : ℝ)) := by
    rw [show (139 / 800 : ℝ) - Real.pi * Real.exp (557 / 800 : ℝ) =
      -(Real.pi * Real.exp (557 / 800 : ℝ) - (139 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (139 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (139 / 200 : ℝ)) := by
    have h := hpThetaJensenCell556_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4589594531733 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell556_endpointUpper :
    hpThetaJensenKernelEndpointUpper (139 / 400 : ℝ) (557 / 1600 : ℝ) ≤ (5333691203 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (557 / 800 : ℝ)) (15756779672078263 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (557 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell556_product_upper
  have hD : (910433697939 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (139 / 200 : ℝ) - (557 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell556_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell556_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (139 / 200 : ℝ) - (557 / 3200 : ℝ)) ≤
      (1 / (910433697939 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (910433697939 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((557 / 3200 : ℝ) - Real.pi * Real.exp (139 / 200 : ℝ)) ≤
      (2 / (910433697939 / 2000000000 : ℝ) : ℝ) := by
    rw [show (557 / 3200 : ℝ) - Real.pi * Real.exp (139 / 200 : ℝ) =
      -(Real.pi * Real.exp (139 / 200 : ℝ) - (557 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (15756779672078263 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (15756779672078263 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell556_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (139 / 400 : ℝ) (557 / 1600 : ℝ)) :
    (2630533957 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5333691203 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell556_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell556_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell557_leftExp :
    (20062152763 / 10000000000 : ℝ) ≤ Real.exp (557 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (557 / 800 : ℝ) (1021996239781 / 1000000000000 : ℝ)
    (20062152763 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell557_rightExp :
    Real.exp (279 / 400 : ℝ) ≤ (4017449227 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (279 / 400 : ℝ) (102203616229 / 100000000000 : ℝ)
    (4017449227 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell557_denomUpper :
    Real.exp (12273065369398611 / 2000000000000000 : ℝ) ≤ (4624473370879 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (12273065369398611 / 2000000000000000 : ℝ) (37855868821 /
    31250000000 : ℝ) (4624473370879 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell557_denomLower :
    (4586717727791 / 10000000000 : ℝ) ≤ Real.exp (7660418577877337 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7660418577877337 / 1250000000000000 : ℝ) (1211077506329
    / 1000000000000 : ℝ) (4586717727791 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell557_product_lower :
    (7878387327877337 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (557 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell557_leftExp
    (by norm_num : (0 : ℝ) ≤ (20062152763 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell557_product_upper :
    Real.pi * Real.exp (279 / 400 : ℝ) ≤ (12621190369398611 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell557_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell557_endpointLower :
    (2618251583 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (557 / 1600 : ℝ) (279 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7878387327877337 / 1250000000000000 : ℝ) (Real.pi * Real.exp (557 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell557_product_lower
  have hD : Real.exp (Real.pi * Real.exp (279 / 400 : ℝ) - (557 / 3200 : ℝ)) ≤
      (4624473370879 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell557_denomUpper
    linarith [hpThetaJensenCell557_product_upper]
  have hi : (1 / (4624473370879 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (279 / 400 : ℝ) - (557 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4624473370879 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4624473370879 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((557 / 3200 : ℝ) - Real.pi * Real.exp (279 / 400 : ℝ)) := by
    rw [show (557 / 3200 : ℝ) - Real.pi * Real.exp (279 / 400 : ℝ) =
      -(Real.pi * Real.exp (279 / 400 : ℝ) - (557 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (557 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (557 / 800 : ℝ)) := by
    have h := hpThetaJensenCell557_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4624473370879 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell557_endpointUpper :
    hpThetaJensenKernelEndpointUpper (557 / 1600 : ℝ) (279 / 800 : ℝ) ≤ (5308836257 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (279 / 400 : ℝ)) (12621190369398611 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (279 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell557_product_upper
  have hD : (4586717727791 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (557 / 800 : ℝ) - (279 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell557_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell557_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (557 / 800 : ℝ) - (279 / 1600 : ℝ)) ≤
      (1 / (4586717727791 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4586717727791 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((279 / 1600 : ℝ) - Real.pi * Real.exp (557 / 800 : ℝ)) ≤
      (2 / (4586717727791 / 10000000000 : ℝ) : ℝ) := by
    rw [show (279 / 1600 : ℝ) - Real.pi * Real.exp (557 / 800 : ℝ) =
      -(Real.pi * Real.exp (557 / 800 : ℝ) - (279 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (12621190369398611 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (12621190369398611 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell557_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (557 / 1600 : ℝ) (279 / 800 : ℝ)) :
    (2618251583 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5308836257 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell557_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell557_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell558_leftExp :
    (10043623067 / 5000000000 : ℝ) ≤ Real.exp (279 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (279 / 400 : ℝ) (1022036162289 / 1000000000000 : ℝ)
    (10043623067 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell558_rightExp :
    Real.exp (559 / 800 : ℝ) ≤ (20112370893 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (559 / 800 : ℝ) (1022076086357 / 1000000000000 : ℝ)
    (20112370893 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell558_denomUpper :
    Real.exp (61441133610852549 / 10000000000000000 : ℝ) ≤ (1164915804969 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (61441133610852549 / 10000000000000000 : ℝ)
    (1211674809357 / 1000000000000 : ℝ) (1164915804969 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell558_denomLower :
    (4621574693043 / 10000000000 : ℝ) ≤ Real.exp (3834941047287833 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3834941047287833 / 625000000000000 : ℝ) (302841016633 /
    250000000000 : ℝ) (4621574693043 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell558_product_lower :
    (3944120734787833 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (279 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell558_leftExp
    (by norm_num : (0 : ℝ) ≤ (10043623067 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell558_product_upper :
    Real.pi * Real.exp (559 / 800 : ℝ) ≤ (63184883610852549 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell558_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell558_endpointLower :
    (325749899 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (279 / 800 : ℝ) (559 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3944120734787833 / 625000000000000 : ℝ) (Real.pi * Real.exp (279 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell558_product_lower
  have hD : Real.exp (Real.pi * Real.exp (559 / 800 : ℝ) - (279 / 1600 : ℝ)) ≤
      (1164915804969 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell558_denomUpper
    linarith [hpThetaJensenCell558_product_upper]
  have hi : (1 / (1164915804969 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (559 / 800 : ℝ) - (279 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1164915804969 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1164915804969 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((279 / 1600 : ℝ) - Real.pi * Real.exp (559 / 800 : ℝ)) := by
    rw [show (279 / 1600 : ℝ) - Real.pi * Real.exp (559 / 800 : ℝ) =
      -(Real.pi * Real.exp (559 / 800 : ℝ) - (279 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (279 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (279 / 400 : ℝ)) := by
    have h := hpThetaJensenCell558_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1164915804969 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell558_endpointUpper :
    hpThetaJensenKernelEndpointUpper (279 / 800 : ℝ) (559 / 1600 : ℝ) ≤ (2642020861 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (559 / 800 : ℝ)) (63184883610852549 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (559 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell558_product_upper
  have hD : (4621574693043 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (279 / 400 : ℝ) - (559 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell558_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell558_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (279 / 400 : ℝ) - (559 / 3200 : ℝ)) ≤
      (1 / (4621574693043 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4621574693043 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((559 / 3200 : ℝ) - Real.pi * Real.exp (279 / 400 : ℝ)) ≤
      (2 / (4621574693043 / 10000000000 : ℝ) : ℝ) := by
    rw [show (559 / 3200 : ℝ) - Real.pi * Real.exp (279 / 400 : ℝ) =
      -(Real.pi * Real.exp (279 / 400 : ℝ) - (559 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (63184883610852549 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (63184883610852549 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell558_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (279 / 800 : ℝ) (559 / 1600 : ℝ)) :
    (325749899 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2642020861 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell558_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell558_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell559_leftExp :
    (20112370891 / 10000000000 : ℝ) ≤ Real.exp (559 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (559 / 800 : ℝ) (255519021589 / 250000000000 : ℝ)
    (20112370891 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell559_rightExp :
    Real.exp (7 / 10 : ℝ) ≤ (5034381769 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7 / 10 : ℝ) (63882250749 / 62500000000 : ℝ)
    (5034381769 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell559_denomUpper :
    Real.exp (15379259774818017 / 2500000000000000 : ℝ) ≤ (4695167197953 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (15379259774818017 / 2500000000000000 : ℝ) (302990564587
    / 250000000000 : ℝ) (4695167197953 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell559_denomLower :
    (465674247139 / 1000000000 : ℝ) ≤ Real.exp (7679357936524809 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7679357936524809 / 1250000000000000 : ℝ) (605825533943 /
    500000000000 : ℝ) (465674247139 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell559_product_lower :
    (7898107936524809 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (559 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell559_leftExp
    (by norm_num : (0 : ℝ) ≤ (20112370891 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell559_product_upper :
    Real.pi * Real.exp (7 / 10 : ℝ) ≤ (15815978524818017 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell559_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell559_endpointLower :
    (324222109 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (559 / 1600 : ℝ) (7 / 20 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7898107936524809 / 1250000000000000 : ℝ) (Real.pi * Real.exp (559 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell559_product_lower
  have hD : Real.exp (Real.pi * Real.exp (7 / 10 : ℝ) - (559 / 3200 : ℝ)) ≤
      (4695167197953 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell559_denomUpper
    linarith [hpThetaJensenCell559_product_upper]
  have hi : (1 / (4695167197953 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (7 / 10 : ℝ) - (559 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4695167197953 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4695167197953 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((559 / 3200 : ℝ) - Real.pi * Real.exp (7 / 10 : ℝ)) := by
    rw [show (559 / 3200 : ℝ) - Real.pi * Real.exp (7 / 10 : ℝ) =
      -(Real.pi * Real.exp (7 / 10 : ℝ) - (559 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (559 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (559 / 800 : ℝ)) := by
    have h := hpThetaJensenCell559_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4695167197953 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell559_endpointUpper :
    hpThetaJensenKernelEndpointUpper (559 / 1600 : ℝ) (7 / 20 : ℝ) ≤ (20544171 / 39062500 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (7 / 10 : ℝ)) (15815978524818017 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (7 / 20 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell559_product_upper
  have hD : (465674247139 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (559 / 800 : ℝ) - (7 / 40 : ℝ)) := by
    apply le_trans hpThetaJensenCell559_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell559_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (559 / 800 : ℝ) - (7 / 40 : ℝ)) ≤
      (1 / (465674247139 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (465674247139 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((7 / 40 : ℝ) - Real.pi * Real.exp (559 / 800 : ℝ)) ≤
      (2 / (465674247139 / 1000000000 : ℝ) : ℝ) := by
    rw [show (7 / 40 : ℝ) - Real.pi * Real.exp (559 / 800 : ℝ) =
      -(Real.pi * Real.exp (559 / 800 : ℝ) - (7 / 40 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (15815978524818017 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (15815978524818017 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell559_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (559 / 1600 : ℝ) (7 / 20 : ℝ)) :
    (324222109 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (20544171 / 39062500 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell559_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell559_endpointUpper

def hpThetaJensenCellsBatch027Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (5662108319 / 10000000000 : ℝ)
  | 1 => (352288101 / 625000000 : ℝ)
  | 2 => (5611167799 / 10000000000 : ℝ)
  | 3 => (2792891537 / 5000000000 : ℝ)
  | 4 => (173764239 / 312500000 : ℝ)
  | 5 => (221407429 / 400000000 : ℝ)
  | 6 => (5509973503 / 10000000000 : ℝ)
  | 7 => (2742409593 / 5000000000 : ℝ)
  | 8 => (5459722969 / 10000000000 : ℝ)
  | 9 => (679335631 / 1250000000 : ℝ)
  | 10 => (2704852809 / 5000000000 : ℝ)
  | 11 => (538478487 / 1000000000 : ℝ)
  | 12 => (334995187 / 625000000 : ℝ)
  | 13 => (5335120173 / 10000000000 : ℝ)
  | 14 => (5310376599 / 10000000000 : ℝ)
  | 15 => (1321423113 / 2500000000 : ℝ)
  | 16 => (2630533957 / 5000000000 : ℝ)
  | 17 => (2618251583 / 5000000000 : ℝ)
  | 18 => (325749899 / 625000000 : ℝ)
  | 19 => (324222109 / 625000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch027Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (5739432291 / 10000000000 : ℝ)
  | 1 => (5713636753 / 10000000000 : ℝ)
  | 2 => (5687898491 / 10000000000 : ℝ)
  | 3 => (1132443543 / 2000000000 : ℝ)
  | 4 => (2818297317 / 5000000000 : ℝ)
  | 5 => (1122205891 / 2000000000 : ℝ)
  | 6 => (1117104477 / 2000000000 : ℝ)
  | 7 => (2780036811 / 5000000000 : ℝ)
  | 8 => (5534683371 / 10000000000 : ℝ)
  | 9 => (688668979 / 1250000000 : ℝ)
  | 10 => (5484079197 / 10000000000 : ℝ)
  | 11 => (5458865663 / 10000000000 : ℝ)
  | 12 => (217348457 / 400000000 : ℝ)
  | 13 => (169019271 / 312500000 : ℝ)
  | 14 => (672947699 / 1250000000 : ℝ)
  | 15 => (42868851 / 80000000 : ℝ)
  | 16 => (5333691203 / 10000000000 : ℝ)
  | 17 => (5308836257 / 10000000000 : ℝ)
  | 18 => (2642020861 / 5000000000 : ℝ)
  | 19 => (20544171 / 39062500 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch027_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((540 : ℝ) + (j.val : ℝ)) / 1600)
      (((540 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch027Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch027Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell540_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell541_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell542_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell543_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell544_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell545_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell546_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell547_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell548_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell549_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell550_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell551_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell552_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell553_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell554_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell555_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell556_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell557_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell558_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell559_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper] at h ⊢
    exact h

end HodgeProofHP
