import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1280_leftExp :
    (49530324243 / 10000000000 : ℝ) ≤ Real.exp (8 / 5 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8 / 5 : ℝ) (131408887047 / 125000000000 : ℝ)
    (49530324243 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1280_rightExp :
    Real.exp (1281 / 800 : ℝ) ≤ (49592275863 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1281 / 800 : ℝ) (131414020307 / 125000000000 : ℝ)
    (49592275863 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1280_denomUpper :
    Real.exp (151798746705269759 / 10000000000000000 : ℝ) ≤ (78264677688149 / 20000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (151798746705269759 / 10000000000000000 : ℝ)
    (803501604349 / 500000000000 : ℝ) (78264677688149 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1280_denomLower :
    (7673180235511083 / 2000000000 : ℝ) ≤ Real.exp (18950118174901857 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (18950118174901857 / 1250000000000000 : ℝ) (1606010180221
    / 1000000000000 : ℝ) (7673180235511083 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1280_product_lower :
    (19450508799901857 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (8 / 5 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1280_leftExp
    (by norm_num : (0 : ℝ) ≤ (49530324243 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1280_product_upper :
    Real.pi * Real.exp (1281 / 800 : ℝ) ≤ (155798746705269759 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1280_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1280_endpointLower :
    (4472733 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (4 / 5 : ℝ) (1281 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (19450508799901857 / 1250000000000000 : ℝ) (Real.pi * Real.exp (8 / 5 : ℝ))
    (by norm_num) hpThetaJensenCell1280_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1281 / 800 : ℝ) - (2 / 5 : ℝ)) ≤
      (78264677688149 / 20000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1280_denomUpper
    linarith [hpThetaJensenCell1280_product_upper]
  have hi : (1 / (78264677688149 / 20000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1281 / 800 : ℝ) - (2 / 5 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (78264677688149 / 20000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (78264677688149 / 20000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((2 / 5 : ℝ) - Real.pi * Real.exp (1281 / 800 : ℝ)) := by
    rw [show (2 / 5 : ℝ) - Real.pi * Real.exp (1281 / 800 : ℝ) =
      -(Real.pi * Real.exp (1281 / 800 : ℝ) - (2 / 5 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (8 / 5 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (8 / 5 : ℝ)) := by
    have h := hpThetaJensenCell1280_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (78264677688149 / 20000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1280_endpointUpper :
    hpThetaJensenKernelEndpointUpper (4 / 5 : ℝ) (1281 / 1600 : ℝ) ≤ (1146541 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1281 / 800 : ℝ)) (155798746705269759 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1281 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1280_product_upper
  have hD : (7673180235511083 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (8 / 5 : ℝ) - (1281 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1280_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1280_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (8 / 5 : ℝ) - (1281 / 3200 : ℝ)) ≤
      (1 / (7673180235511083 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (7673180235511083 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1281 / 3200 : ℝ) - Real.pi * Real.exp (8 / 5 : ℝ)) ≤
      (2 / (7673180235511083 / 2000000000 : ℝ) : ℝ) := by
    rw [show (1281 / 3200 : ℝ) - Real.pi * Real.exp (8 / 5 : ℝ) =
      -(Real.pi * Real.exp (8 / 5 : ℝ) - (1281 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (155798746705269759 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (155798746705269759 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1280_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (4 / 5 : ℝ) (1281 / 1600 : ℝ)) :
    (4472733 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1146541 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1280_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1280_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1281_leftExp :
    (2479613793 / 500000000 : ℝ) ≤ Real.exp (1281 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1281 / 800 : ℝ) (210262432491 / 200000000000 : ℝ)
    (2479613793 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1281_rightExp :
    Real.exp (641 / 400 : ℝ) ≤ (49654304967 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (641 / 400 : ℝ) (1051353230139 / 1000000000000 : ℝ)
    (49654304967 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1281_denomUpper :
    Real.exp (151990491904192431 / 10000000000000000 : ℝ) ≤ (4986240324417421 / 1250000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (151990491904192431 / 10000000000000000 : ℝ)
    (1607966419593 / 1000000000000 : ℝ) (4986240324417421 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1281_denomLower :
    (39107694791712633 / 10000000000 : ℝ) ≤ Real.exp (948702794397307 / 62500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (948702794397307 / 62500000000000 : ℝ) (1606971573133 /
    1000000000000 : ℝ) (39107694791712633 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1281_product_lower :
    (973741856897307 / 62500000000000 : ℝ) ≤ Real.pi * Real.exp (1281 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1281_leftExp
    (by norm_num : (0 : ℝ) ≤ (2479613793 / 500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1281_product_upper :
    Real.pi * Real.exp (641 / 400 : ℝ) ≤ (155993616904192431 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1281_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1281_endpointLower :
    (4399357 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1281 / 1600 : ℝ) (641 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (973741856897307 / 62500000000000 : ℝ) (Real.pi * Real.exp (1281 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1281_product_lower
  have hD : Real.exp (Real.pi * Real.exp (641 / 400 : ℝ) - (1281 / 3200 : ℝ)) ≤
      (4986240324417421 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1281_denomUpper
    linarith [hpThetaJensenCell1281_product_upper]
  have hi : (1 / (4986240324417421 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (641 / 400 : ℝ) - (1281 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4986240324417421 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4986240324417421 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1281 / 3200 : ℝ) - Real.pi * Real.exp (641 / 400 : ℝ)) := by
    rw [show (1281 / 3200 : ℝ) - Real.pi * Real.exp (641 / 400 : ℝ) =
      -(Real.pi * Real.exp (641 / 400 : ℝ) - (1281 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1281 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1281 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1281_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4986240324417421 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1281_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1281 / 1600 : ℝ) (641 / 800 : ℝ) ≤ (1127759 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (641 / 400 : ℝ)) (155993616904192431 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (641 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1281_product_upper
  have hD : (39107694791712633 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1281 / 800 : ℝ) - (641 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1281_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1281_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1281 / 800 : ℝ) - (641 / 1600 : ℝ)) ≤
      (1 / (39107694791712633 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (39107694791712633 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((641 / 1600 : ℝ) - Real.pi * Real.exp (1281 / 800 : ℝ)) ≤
      (2 / (39107694791712633 / 10000000000 : ℝ) : ℝ) := by
    rw [show (641 / 1600 : ℝ) - Real.pi * Real.exp (1281 / 800 : ℝ) =
      -(Real.pi * Real.exp (1281 / 800 : ℝ) - (641 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (155993616904192431 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (155993616904192431 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1281_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1281 / 1600 : ℝ) (641 / 800 : ℝ)) :
    (4399357 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1127759 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1281_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1281_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1282_leftExp :
    (12413576241 / 2500000000 : ℝ) ≤ Real.exp (641 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (641 / 400 : ℝ) (525676615069 / 500000000000 : ℝ)
    (12413576241 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1282_rightExp :
    Real.exp (1283 / 800 : ℝ) ≤ (49716411657 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1283 / 800 : ℝ) (1051394299427 / 1000000000000 : ℝ)
    (49716411657 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1282_denomUpper :
    Real.exp (152182480846749601 / 10000000000000000 : ℝ) ≤ (40663163939609087 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (152182480846749601 / 10000000000000000 : ℝ)
    (1608931433341 / 1000000000000 : ℝ) (40663163939609087 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1282_denomLower :
    (39864801198002463 / 10000000000 : ℝ) ≤ Real.exp (4749506007514459 / 312500000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (4749506007514459 / 312500000000000 : ℝ) (803967382377 /
    500000000000 : ℝ) (39864801198002463 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1282_product_lower :
    (4874798976264459 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (641 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1282_leftExp
    (by norm_num : (0 : ℝ) ≤ (12413576241 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1282_product_upper :
    Real.pi * Real.exp (1283 / 800 : ℝ) ≤ (156188730846749601 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1282_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1282_endpointLower :
    (2163539 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (641 / 800 : ℝ) (1283 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4874798976264459 / 312500000000000 : ℝ) (Real.pi * Real.exp (641 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1282_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1283 / 800 : ℝ) - (641 / 1600 : ℝ)) ≤
      (40663163939609087 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1282_denomUpper
    linarith [hpThetaJensenCell1282_product_upper]
  have hi : (1 / (40663163939609087 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1283 / 800 : ℝ) - (641 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (40663163939609087 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (40663163939609087 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((641 / 1600 : ℝ) - Real.pi * Real.exp (1283 / 800 : ℝ)) := by
    rw [show (641 / 1600 : ℝ) - Real.pi * Real.exp (1283 / 800 : ℝ) =
      -(Real.pi * Real.exp (1283 / 800 : ℝ) - (641 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (641 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (641 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1282_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (40663163939609087 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1282_endpointUpper :
    hpThetaJensenKernelEndpointUpper (641 / 800 : ℝ) (1283 / 1600 : ℝ) ≤ (443703 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1283 / 800 : ℝ)) (156188730846749601 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1283 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1282_product_upper
  have hD : (39864801198002463 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (641 / 400 : ℝ) - (1283 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1282_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1282_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (641 / 400 : ℝ) - (1283 / 3200 : ℝ)) ≤
      (1 / (39864801198002463 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (39864801198002463 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1283 / 3200 : ℝ) - Real.pi * Real.exp (641 / 400 : ℝ)) ≤
      (2 / (39864801198002463 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1283 / 3200 : ℝ) - Real.pi * Real.exp (641 / 400 : ℝ) =
      -(Real.pi * Real.exp (641 / 400 : ℝ) - (1283 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (156188730846749601 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (156188730846749601 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1282_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (641 / 800 : ℝ) (1283 / 1600 : ℝ)) :
    (2163539 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (443703 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1282_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1282_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1283_leftExp :
    (9943282331 / 2000000000 : ℝ) ≤ Real.exp (1283 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1283 / 800 : ℝ) (525697149713 / 500000000000 : ℝ)
    (9943282331 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1283_rightExp :
    Real.exp (321 / 200 : ℝ) ≤ (49778596029 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (321 / 200 : ℝ) (1051435370319 / 1000000000000 : ℝ)
    (49778596029 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1283_denomUpper :
    Real.exp (152374713834534197 / 10000000000000000 : ℝ) ≤ (2072620284971233 / 500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (152374713834534197 / 10000000000000000 : ℝ)
    (1609898254011 / 1000000000000 : ℝ) (2072620284971233 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1283_denomLower :
    (2539847208747817 / 625000000 : ℝ) ≤ Real.exp (3804404528101369 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3804404528101369 / 250000000000000 : ℝ) (201112469901 /
    125000000000 : ℝ) (2539847208747817 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1283_product_lower :
    (3904717028101369 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1283 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1283_leftExp
    (by norm_num : (0 : ℝ) ≤ (9943282331 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1283_product_upper :
    Real.pi * Real.exp (321 / 200 : ℝ) ≤ (156384088834534197 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1283_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1283_endpointLower :
    (4255883 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1283 / 1600 : ℝ) (321 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3904717028101369 / 250000000000000 : ℝ) (Real.pi * Real.exp (1283 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1283_product_lower
  have hD : Real.exp (Real.pi * Real.exp (321 / 200 : ℝ) - (1283 / 3200 : ℝ)) ≤
      (2072620284971233 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1283_denomUpper
    linarith [hpThetaJensenCell1283_product_upper]
  have hi : (1 / (2072620284971233 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (321 / 200 : ℝ) - (1283 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2072620284971233 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2072620284971233 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1283 / 3200 : ℝ) - Real.pi * Real.exp (321 / 200 : ℝ)) := by
    rw [show (1283 / 3200 : ℝ) - Real.pi * Real.exp (321 / 200 : ℝ) =
      -(Real.pi * Real.exp (321 / 200 : ℝ) - (1283 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1283 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1283 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1283_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2072620284971233 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1283_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1283 / 1600 : ℝ) (321 / 400 : ℝ) ≤ (4364131 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (321 / 200 : ℝ)) (156384088834534197 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (321 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1283_product_upper
  have hD : (2539847208747817 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1283 / 800 : ℝ) - (321 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1283_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1283_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1283 / 800 : ℝ) - (321 / 800 : ℝ)) ≤
      (1 / (2539847208747817 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2539847208747817 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((321 / 800 : ℝ) - Real.pi * Real.exp (1283 / 800 : ℝ)) ≤
      (2 / (2539847208747817 / 625000000 : ℝ) : ℝ) := by
    rw [show (321 / 800 : ℝ) - Real.pi * Real.exp (1283 / 800 : ℝ) =
      -(Real.pi * Real.exp (1283 / 800 : ℝ) - (321 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (156384088834534197 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (156384088834534197 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1283_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1283 / 1600 : ℝ) (321 / 400 : ℝ)) :
    (4255883 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4364131 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1283_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1283_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1284_leftExp :
    (24889298013 / 5000000000 : ℝ) ≤ Real.exp (321 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (321 / 200 : ℝ) (525717685159 / 500000000000 : ℝ)
    (24889298013 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1284_rightExp :
    Real.exp (257 / 160 : ℝ) ≤ (49840858179 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (257 / 160 : ℝ) (210295288563 / 200000000000 : ℝ)
    (49840858179 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1284_denomUpper :
    Real.exp (152567191169139147 / 10000000000000000 : ℝ) ≤ (10564499651064439 / 2500000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (152567191169139147 / 10000000000000000 : ℝ)
    (322173377137 / 200000000000 : ℝ) (10564499651064439 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1284_denomLower :
    (103565749465087 / 25000000 : ℝ) ≤ Real.exp (9523025877907087 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9523025877907087 / 625000000000000 : ℝ) (1609866560517 /
    1000000000000 : ℝ) (103565749465087 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1284_product_lower :
    (9774002440407087 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (321 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1284_leftExp
    (by norm_num : (0 : ℝ) ≤ (24889298013 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1284_product_upper :
    Real.pi * Real.exp (257 / 160 : ℝ) ≤ (156579691169139147 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1284_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1284_endpointLower :
    (837151 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (321 / 400 : ℝ) (257 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9774002440407087 / 625000000000000 : ℝ) (Real.pi * Real.exp (321 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1284_product_lower
  have hD : Real.exp (Real.pi * Real.exp (257 / 160 : ℝ) - (321 / 800 : ℝ)) ≤
      (10564499651064439 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1284_denomUpper
    linarith [hpThetaJensenCell1284_product_upper]
  have hi : (1 / (10564499651064439 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (257 / 160 : ℝ) - (321 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (10564499651064439 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (10564499651064439 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((321 / 800 : ℝ) - Real.pi * Real.exp (257 / 160 : ℝ)) := by
    rw [show (321 / 800 : ℝ) - Real.pi * Real.exp (257 / 160 : ℝ) =
      -(Real.pi * Real.exp (257 / 160 : ℝ) - (321 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (321 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (321 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1284_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (10564499651064439 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1284_endpointUpper :
    hpThetaJensenKernelEndpointUpper (321 / 400 : ℝ) (257 / 320 : ℝ) ≤ (1073081 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (257 / 160 : ℝ)) (156579691169139147 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (257 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1284_product_upper
  have hD : (103565749465087 / 25000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (321 / 200 : ℝ) - (257 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1284_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1284_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (321 / 200 : ℝ) - (257 / 640 : ℝ)) ≤
      (1 / (103565749465087 / 25000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (103565749465087 / 25000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((257 / 640 : ℝ) - Real.pi * Real.exp (321 / 200 : ℝ)) ≤
      (2 / (103565749465087 / 25000000 : ℝ) : ℝ) := by
    rw [show (257 / 640 : ℝ) - Real.pi * Real.exp (321 / 200 : ℝ) =
      -(Real.pi * Real.exp (321 / 200 : ℝ) - (257 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (156579691169139147 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (156579691169139147 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1284_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (321 / 400 : ℝ) (257 / 320 : ℝ)) :
    (837151 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1073081 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1284_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1284_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1285_leftExp :
    (49840858177 / 10000000000 : ℝ) ≤ Real.exp (257 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (257 / 160 : ℝ) (525738221407 / 500000000000 : ℝ)
    (49840858177 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1285_rightExp :
    Real.exp (643 / 400 : ℝ) ≤ (49903198207 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (643 / 400 : ℝ) (262879379229 / 250000000000 : ℝ)
    (49903198207 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1285_denomUpper :
    Real.exp (152759913164723751 / 10000000000000000 : ℝ) ≤ (10770075381979203 / 2500000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (152759913164723751 / 10000000000000000 : ℝ) (50369916641
    / 31250000000 : ℝ) (10770075381979203 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1285_denomLower :
    (42231385093476371 / 10000000000 : ℝ) ≤ Real.exp (19070111415249723 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (19070111415249723 / 1250000000000000 : ℝ) (1610835172823
    / 1000000000000 : ℝ) (42231385093476371 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1285_product_lower :
    (19572455165249723 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (257 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1285_leftExp
    (by norm_num : (0 : ℝ) ≤ (49840858177 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1285_product_upper :
    Real.pi * Real.exp (643 / 400 : ℝ) ≤ (156775538164723751 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1285_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1285_endpointLower :
    (2058341 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (257 / 320 : ℝ) (643 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (19572455165249723 / 1250000000000000 : ℝ) (Real.pi * Real.exp (257 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1285_product_lower
  have hD : Real.exp (Real.pi * Real.exp (643 / 400 : ℝ) - (257 / 640 : ℝ)) ≤
      (10770075381979203 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1285_denomUpper
    linarith [hpThetaJensenCell1285_product_upper]
  have hi : (1 / (10770075381979203 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (643 / 400 : ℝ) - (257 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (10770075381979203 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (10770075381979203 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((257 / 640 : ℝ) - Real.pi * Real.exp (643 / 400 : ℝ)) := by
    rw [show (257 / 640 : ℝ) - Real.pi * Real.exp (643 / 400 : ℝ) =
      -(Real.pi * Real.exp (643 / 400 : ℝ) - (257 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (257 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (257 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1285_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (10770075381979203 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1285_endpointUpper :
    hpThetaJensenKernelEndpointUpper (257 / 320 : ℝ) (643 / 800 : ℝ) ≤ (844319 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (643 / 400 : ℝ)) (156775538164723751 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (643 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1285_product_upper
  have hD : (42231385093476371 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (257 / 160 : ℝ) - (643 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1285_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1285_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (257 / 160 : ℝ) - (643 / 1600 : ℝ)) ≤
      (1 / (42231385093476371 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (42231385093476371 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((643 / 1600 : ℝ) - Real.pi * Real.exp (257 / 160 : ℝ)) ≤
      (2 / (42231385093476371 / 10000000000 : ℝ) : ℝ) := by
    rw [show (643 / 1600 : ℝ) - Real.pi * Real.exp (257 / 160 : ℝ) =
      -(Real.pi * Real.exp (257 / 160 : ℝ) - (643 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (156775538164723751 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (156775538164723751 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1285_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (257 / 320 : ℝ) (643 / 800 : ℝ)) :
    (2058341 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (844319 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1285_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1285_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1286_leftExp :
    (12475799551 / 2500000000 : ℝ) ≤ Real.exp (643 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (643 / 400 : ℝ) (210303503383 / 200000000000 : ℝ)
    (12475799551 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1286_rightExp :
    Real.exp (1287 / 800 : ℝ) ≤ (49965616207 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1287 / 800 : ℝ) (1051558592621 / 1000000000000 : ℝ)
    (49965616207 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1286_denomUpper :
    Real.exp (152952880116597751 / 10000000000000000 : ℝ) ≤ (43919681559114469 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (152952880116597751 / 10000000000000000 : ℝ)
    (1612809598559 / 1000000000000 : ℝ) (43919681559114469 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1286_denomLower :
    (43053169859925553 / 10000000000 : ℝ) ≤ Real.exp (4773550414128149 / 312500000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (4773550414128149 / 312500000000000 : ℝ) (322361120043 /
    200000000000 : ℝ) (43053169859925553 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1286_product_lower :
    (4899234007878149 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (643 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1286_leftExp
    (by norm_num : (0 : ℝ) ≤ (12475799551 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1286_product_upper :
    Real.pi * Real.exp (1287 / 800 : ℝ) ≤ (156971630116597751 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1286_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1286_endpointLower :
    (506081 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (643 / 800 : ℝ) (1287 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4899234007878149 / 312500000000000 : ℝ) (Real.pi * Real.exp (643 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1286_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1287 / 800 : ℝ) - (643 / 1600 : ℝ)) ≤
      (43919681559114469 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1286_denomUpper
    linarith [hpThetaJensenCell1286_product_upper]
  have hi : (1 / (43919681559114469 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1287 / 800 : ℝ) - (643 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (43919681559114469 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (43919681559114469 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((643 / 1600 : ℝ) - Real.pi * Real.exp (1287 / 800 : ℝ)) := by
    rw [show (643 / 1600 : ℝ) - Real.pi * Real.exp (1287 / 800 : ℝ) =
      -(Real.pi * Real.exp (1287 / 800 : ℝ) - (643 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (643 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (643 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1286_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (43919681559114469 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1286_endpointUpper :
    hpThetaJensenKernelEndpointUpper (643 / 800 : ℝ) (1287 / 1600 : ℝ) ≤ (4151929 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1287 / 800 : ℝ)) (156971630116597751 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1287 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1286_product_upper
  have hD : (43053169859925553 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (643 / 400 : ℝ) - (1287 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1286_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1286_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (643 / 400 : ℝ) - (1287 / 3200 : ℝ)) ≤
      (1 / (43053169859925553 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (43053169859925553 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1287 / 3200 : ℝ) - Real.pi * Real.exp (643 / 400 : ℝ)) ≤
      (2 / (43053169859925553 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1287 / 3200 : ℝ) - Real.pi * Real.exp (643 / 400 : ℝ) =
      -(Real.pi * Real.exp (643 / 400 : ℝ) - (1287 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (156971630116597751 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (156971630116597751 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1286_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (643 / 800 : ℝ) (1287 / 1600 : ℝ)) :
    (506081 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4151929 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1286_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1286_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1287_leftExp :
    (12491404051 / 2500000000 : ℝ) ≤ Real.exp (1287 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1287 / 800 : ℝ) (52577929631 / 50000000000 : ℝ)
    (12491404051 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1287_rightExp :
    Real.exp (161 / 100 : ℝ) ≤ (50028112279 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (161 / 100 : ℝ) (1051599669931 / 1000000000000 : ℝ)
    (50028112279 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1287_denomUpper :
    Real.exp (153146092338920447 / 10000000000000000 : ℝ) ≤ (11194128589994249 / 2500000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (153146092338920447 / 10000000000000000 : ℝ)
    (1613783687997 / 1000000000000 : ℝ) (11194128589994249 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1287_denomLower :
    (10973005245528129 / 2500000000 : ℝ) ≤ Real.exp (4779580629423649 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4779580629423649 / 312500000000000 : ℝ) (1612777846807 /
    1000000000000 : ℝ) (10973005245528129 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1287_product_lower :
    (4905361879423649 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (1287 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1287_leftExp
    (by norm_num : (0 : ℝ) ≤ (12491404051 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1287_product_upper :
    Real.pi * Real.exp (161 / 100 : ℝ) ≤ (157167967338920447 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1287_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1287_endpointLower :
    (3981641 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1287 / 1600 : ℝ) (161 / 200 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4905361879423649 / 312500000000000 : ℝ) (Real.pi * Real.exp (1287 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1287_product_lower
  have hD : Real.exp (Real.pi * Real.exp (161 / 100 : ℝ) - (1287 / 3200 : ℝ)) ≤
      (11194128589994249 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1287_denomUpper
    linarith [hpThetaJensenCell1287_product_upper]
  have hi : (1 / (11194128589994249 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (161 / 100 : ℝ) - (1287 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (11194128589994249 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (11194128589994249 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1287 / 3200 : ℝ) - Real.pi * Real.exp (161 / 100 : ℝ)) := by
    rw [show (1287 / 3200 : ℝ) - Real.pi * Real.exp (161 / 100 : ℝ) =
      -(Real.pi * Real.exp (161 / 100 : ℝ) - (1287 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1287 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1287 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1287_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (11194128589994249 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1287_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1287 / 1600 : ℝ) (161 / 200 : ℝ) ≤ (4083311 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (161 / 100 : ℝ)) (157167967338920447 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (161 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1287_product_upper
  have hD : (10973005245528129 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1287 / 800 : ℝ) - (161 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1287_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1287_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1287 / 800 : ℝ) - (161 / 400 : ℝ)) ≤
      (1 / (10973005245528129 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (10973005245528129 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((161 / 400 : ℝ) - Real.pi * Real.exp (1287 / 800 : ℝ)) ≤
      (2 / (10973005245528129 / 2500000000 : ℝ) : ℝ) := by
    rw [show (161 / 400 : ℝ) - Real.pi * Real.exp (1287 / 800 : ℝ) =
      -(Real.pi * Real.exp (1287 / 800 : ℝ) - (161 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (157167967338920447 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (157167967338920447 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1287_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1287 / 1600 : ℝ) (161 / 200 : ℝ)) :
    (3981641 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4083311 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1287_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1287_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1288_leftExp :
    (50028112277 / 10000000000 : ℝ) ≤ Real.exp (161 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (161 / 100 : ℝ) (105159966993 / 100000000000 : ℝ)
    (50028112277 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1288_rightExp :
    Real.exp (1289 / 800 : ℝ) ≤ (50090686521 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1289 / 800 : ℝ) (525820374423 / 500000000000 : ℝ)
    (50090686521 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1288_denomUpper :
    Real.exp (153339550139567953 / 10000000000000000 : ℝ) ≤ (45651184265660511 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (153339550139567953 / 10000000000000000 : ℝ) (64590384199
    / 40000000000 : ℝ) (45651184265660511 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1288_denomLower :
    (44748313885220673 / 10000000000 : ℝ) ≤ Real.exp (19142474038065623 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (19142474038065623 / 1250000000000000 : ℝ) (1613751916769
    / 1000000000000 : ℝ) (44748313885220673 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1288_product_lower :
    (19645989663065623 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (161 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1288_leftExp
    (by norm_num : (0 : ℝ) ≤ (50028112277 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1288_product_upper :
    Real.pi * Real.exp (1289 / 800 : ℝ) ≤ (157364550139567953 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1288_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1288_endpointLower :
    (1957823 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (161 / 200 : ℝ) (1289 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (19645989663065623 / 1250000000000000 : ℝ) (Real.pi * Real.exp (161 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1288_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1289 / 800 : ℝ) - (161 / 400 : ℝ)) ≤
      (45651184265660511 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1288_denomUpper
    linarith [hpThetaJensenCell1288_product_upper]
  have hi : (1 / (45651184265660511 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1289 / 800 : ℝ) - (161 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (45651184265660511 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (45651184265660511 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((161 / 400 : ℝ) - Real.pi * Real.exp (1289 / 800 : ℝ)) := by
    rw [show (161 / 400 : ℝ) - Real.pi * Real.exp (1289 / 800 : ℝ) =
      -(Real.pi * Real.exp (1289 / 800 : ℝ) - (161 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (161 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (161 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1288_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (45651184265660511 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1288_endpointUpper :
    hpThetaJensenKernelEndpointUpper (161 / 200 : ℝ) (1289 / 1600 : ℝ) ≤ (4015729 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1289 / 800 : ℝ)) (157364550139567953 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1289 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1288_product_upper
  have hD : (44748313885220673 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (161 / 100 : ℝ) - (1289 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1288_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1288_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (161 / 100 : ℝ) - (1289 / 3200 : ℝ)) ≤
      (1 / (44748313885220673 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (44748313885220673 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1289 / 3200 : ℝ) - Real.pi * Real.exp (161 / 100 : ℝ)) ≤
      (2 / (44748313885220673 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1289 / 3200 : ℝ) - Real.pi * Real.exp (161 / 100 : ℝ) =
      -(Real.pi * Real.exp (161 / 100 : ℝ) - (1289 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (157364550139567953 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (157364550139567953 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1288_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (161 / 200 : ℝ) (1289 / 1600 : ℝ)) :
    (1957823 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4015729 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1288_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1288_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1289_leftExp :
    (50090686519 / 10000000000 : ℝ) ≤ Real.exp (1289 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1289 / 800 : ℝ) (210328149769 / 200000000000 : ℝ)
    (50090686519 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1289_rightExp :
    Real.exp (129 / 80 : ℝ) ≤ (50153339029 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (129 / 80 : ℝ) (210336365873 / 200000000000 : ℝ)
    (50153339029 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1289_denomUpper :
    Real.exp (153533253820133197 / 10000000000000000 : ℝ) ≤ (1861763379639861 / 400000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (153533253820133197 / 10000000000000000 : ℝ)
    (807868676809 / 500000000000 : ℝ) (1861763379639861 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1289_denomLower :
    (5702804079241693 / 1250000000 : ℝ) ≤ Real.exp (19166656255324781 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (19166656255324781 / 1250000000000000 : ℝ) (807363907109
    / 500000000000 : ℝ) (5702804079241693 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1289_product_lower :
    (19670562505324781 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1289 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1289_leftExp
    (by norm_num : (0 : ℝ) ≤ (50090686519 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1289_product_upper :
    Real.pi * Real.exp (129 / 80 : ℝ) ≤ (157561378820133197 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1289_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1289_endpointLower :
    (3850649 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1289 / 1600 : ℝ) (129 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (19670562505324781 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1289 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1289_product_lower
  have hD : Real.exp (Real.pi * Real.exp (129 / 80 : ℝ) - (1289 / 3200 : ℝ)) ≤
      (1861763379639861 / 400000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1289_denomUpper
    linarith [hpThetaJensenCell1289_product_upper]
  have hi : (1 / (1861763379639861 / 400000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (129 / 80 : ℝ) - (1289 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1861763379639861 / 400000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1861763379639861 / 400000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1289 / 3200 : ℝ) - Real.pi * Real.exp (129 / 80 : ℝ)) := by
    rw [show (1289 / 3200 : ℝ) - Real.pi * Real.exp (129 / 80 : ℝ) =
      -(Real.pi * Real.exp (129 / 80 : ℝ) - (1289 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1289 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1289 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1289_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1861763379639861 / 400000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1289_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1289 / 1600 : ℝ) (129 / 160 : ℝ) ≤ (3949167 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (129 / 80 : ℝ)) (157561378820133197 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (129 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1289_product_upper
  have hD : (5702804079241693 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1289 / 800 : ℝ) - (129 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell1289_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1289_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1289 / 800 : ℝ) - (129 / 320 : ℝ)) ≤
      (1 / (5702804079241693 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5702804079241693 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((129 / 320 : ℝ) - Real.pi * Real.exp (1289 / 800 : ℝ)) ≤
      (2 / (5702804079241693 / 1250000000 : ℝ) : ℝ) := by
    rw [show (129 / 320 : ℝ) - Real.pi * Real.exp (1289 / 800 : ℝ) =
      -(Real.pi * Real.exp (1289 / 800 : ℝ) - (129 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (157561378820133197 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (157561378820133197 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1289_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1289 / 1600 : ℝ) (129 / 160 : ℝ)) :
    (3850649 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3949167 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1289_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1289_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1290_leftExp :
    (50153339027 / 10000000000 : ℝ) ≤ Real.exp (129 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (129 / 80 : ℝ) (262920457341 / 250000000000 : ℝ)
    (50153339027 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1290_rightExp :
    Real.exp (1291 / 800 : ℝ) ≤ (502160699 / 100000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1291 / 800 : ℝ) (4108292623 / 3906250000 : ℝ)
    (502160699 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1290_denomUpper :
    Real.exp (1537272036853507 / 100000000000000 : ℝ) ≤ (23727808696417083 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1537272036853507 / 100000000000000 : ℝ) (1616716938079 /
    1000000000000 : ℝ) (23727808696417083 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1290_denomLower :
    (46514770209072217 / 10000000000 : ℝ) ≤ Real.exp (19190869207563873 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (19190869207563873 / 1250000000000000 : ℝ) (323141108659
    / 200000000000 : ℝ) (46514770209072217 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1290_product_lower :
    (19695166082563873 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (129 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1290_leftExp
    (by norm_num : (0 : ℝ) ≤ (50153339027 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1290_product_upper :
    Real.pi * Real.exp (1291 / 800 : ℝ) ≤ (1577584536853507 / 100000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1290_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1290_endpointLower :
    (3786637 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (129 / 160 : ℝ) (1291 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (19695166082563873 / 1250000000000000 : ℝ) (Real.pi * Real.exp (129 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell1290_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1291 / 800 : ℝ) - (129 / 320 : ℝ)) ≤
      (23727808696417083 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1290_denomUpper
    linarith [hpThetaJensenCell1290_product_upper]
  have hi : (1 / (23727808696417083 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1291 / 800 : ℝ) - (129 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (23727808696417083 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (23727808696417083 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((129 / 320 : ℝ) - Real.pi * Real.exp (1291 / 800 : ℝ)) := by
    rw [show (129 / 320 : ℝ) - Real.pi * Real.exp (1291 / 800 : ℝ) =
      -(Real.pi * Real.exp (1291 / 800 : ℝ) - (129 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (129 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (129 / 80 : ℝ)) := by
    have h := hpThetaJensenCell1290_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (23727808696417083 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1290_endpointUpper :
    hpThetaJensenKernelEndpointUpper (129 / 160 : ℝ) (1291 / 1600 : ℝ) ≤ (970903 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1291 / 800 : ℝ)) (1577584536853507 / 100000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1291 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1290_product_upper
  have hD : (46514770209072217 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (129 / 80 : ℝ) - (1291 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1290_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1290_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (129 / 80 : ℝ) - (1291 / 3200 : ℝ)) ≤
      (1 / (46514770209072217 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (46514770209072217 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1291 / 3200 : ℝ) - Real.pi * Real.exp (129 / 80 : ℝ)) ≤
      (2 / (46514770209072217 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1291 / 3200 : ℝ) - Real.pi * Real.exp (129 / 80 : ℝ) =
      -(Real.pi * Real.exp (129 / 80 : ℝ) - (1291 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1577584536853507 / 100000000000000 : ℝ) ^ 2 - 6 *
      (1577584536853507 / 100000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1290_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (129 / 160 : ℝ) (1291 / 1600 : ℝ)) :
    (3786637 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (970903 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1290_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1290_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1291_leftExp :
    (25108034949 / 5000000000 : ℝ) ≤ Real.exp (1291 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1291 / 800 : ℝ) (1051722911487 / 1000000000000 : ℝ)
    (25108034949 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1291_rightExp :
    Real.exp (323 / 200 : ℝ) ≤ (12569719809 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (323 / 200 : ℝ) (1051763995217 / 1000000000000 : ℝ)
    (12569719809 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1291_denomUpper :
    Real.exp (38480350013915737 / 2500000000000000 : ℝ) ≤ (24193097374977093 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (38480350013915737 / 2500000000000000 : ℝ) (808849181299
    / 500000000000 : ℝ) (24193097374977093 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1291_denomLower :
    (47425728713778493 / 10000000000 : ℝ) ≤ Real.exp (9607556466437351 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (9607556466437351 / 625000000000000 : ℝ) (1616685108153 /
    1000000000000 : ℝ) (47425728713778493 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1291_product_lower :
    (9859900216437351 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1291 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1291_leftExp
    (by norm_num : (0 : ℝ) ≤ (25108034949 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1291_product_upper :
    Real.pi * Real.exp (323 / 200 : ℝ) ≤ (39488943763915737 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1291_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1291_endpointLower :
    (3723597 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1291 / 1600 : ℝ) (323 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9859900216437351 / 625000000000000 : ℝ) (Real.pi * Real.exp (1291 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1291_product_lower
  have hD : Real.exp (Real.pi * Real.exp (323 / 200 : ℝ) - (1291 / 3200 : ℝ)) ≤
      (24193097374977093 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1291_denomUpper
    linarith [hpThetaJensenCell1291_product_upper]
  have hi : (1 / (24193097374977093 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (323 / 200 : ℝ) - (1291 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (24193097374977093 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (24193097374977093 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1291 / 3200 : ℝ) - Real.pi * Real.exp (323 / 200 : ℝ)) := by
    rw [show (1291 / 3200 : ℝ) - Real.pi * Real.exp (323 / 200 : ℝ) =
      -(Real.pi * Real.exp (323 / 200 : ℝ) - (1291 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1291 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1291 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1291_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (24193097374977093 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1291_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1291 / 1600 : ℝ) (323 / 400 : ℝ) ≤ (3819051 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (323 / 200 : ℝ)) (39488943763915737 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (323 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1291_product_upper
  have hD : (47425728713778493 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1291 / 800 : ℝ) - (323 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1291_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1291_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1291 / 800 : ℝ) - (323 / 800 : ℝ)) ≤
      (1 / (47425728713778493 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (47425728713778493 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((323 / 800 : ℝ) - Real.pi * Real.exp (1291 / 800 : ℝ)) ≤
      (2 / (47425728713778493 / 10000000000 : ℝ) : ℝ) := by
    rw [show (323 / 800 : ℝ) - Real.pi * Real.exp (1291 / 800 : ℝ) =
      -(Real.pi * Real.exp (1291 / 800 : ℝ) - (323 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (39488943763915737 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (39488943763915737 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1291_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1291 / 1600 : ℝ) (323 / 400 : ℝ)) :
    (3723597 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3819051 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1291_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1291_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1292_leftExp :
    (50278879233 / 10000000000 : ℝ) ≤ Real.exp (323 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (323 / 200 : ℝ) (65735249701 / 62500000000 : ℝ)
    (50278879233 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1292_rightExp :
    Real.exp (1293 / 800 : ℝ) ≤ (12585441783 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1293 / 800 : ℝ) (1051805080551 / 1000000000000 : ℝ)
    (12585441783 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1292_denomUpper :
    Real.exp (38528960807380319 / 2500000000000000 : ℝ) ≤ (9867247563043467 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (38528960807380319 / 2500000000000000 : ℝ) (323736326263
    / 200000000000 : ℝ) (9867247563043467 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1292_denomLower :
    (48355719652839597 / 10000000000 : ℝ) ≤ Real.exp (19239387470919867 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (19239387470919867 / 1250000000000000 : ℝ) (1617666513017
    / 1000000000000 : ℝ) (48355719652839597 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1292_product_lower :
    (19744465595919867 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (323 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1292_leftExp
    (by norm_num : (0 : ℝ) ≤ (50278879233 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1292_product_upper :
    Real.pi * Real.exp (1293 / 800 : ℝ) ≤ (39538335807380319 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1292_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1292_endpointLower :
    (732303 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (323 / 400 : ℝ) (1293 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (19744465595919867 / 1250000000000000 : ℝ) (Real.pi * Real.exp (323 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1292_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1293 / 800 : ℝ) - (323 / 800 : ℝ)) ≤
      (9867247563043467 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1292_denomUpper
    linarith [hpThetaJensenCell1292_product_upper]
  have hi : (1 / (9867247563043467 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1293 / 800 : ℝ) - (323 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (9867247563043467 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (9867247563043467 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((323 / 800 : ℝ) - Real.pi * Real.exp (1293 / 800 : ℝ)) := by
    rw [show (323 / 800 : ℝ) - Real.pi * Real.exp (1293 / 800 : ℝ) =
      -(Real.pi * Real.exp (1293 / 800 : ℝ) - (323 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (323 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (323 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1292_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (9867247563043467 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1292_endpointUpper :
    hpThetaJensenKernelEndpointUpper (323 / 400 : ℝ) (1293 / 1600 : ℝ) ≤ (375547 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1293 / 800 : ℝ)) (39538335807380319 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1293 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1292_product_upper
  have hD : (48355719652839597 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (323 / 200 : ℝ) - (1293 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1292_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1292_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (323 / 200 : ℝ) - (1293 / 3200 : ℝ)) ≤
      (1 / (48355719652839597 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (48355719652839597 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1293 / 3200 : ℝ) - Real.pi * Real.exp (323 / 200 : ℝ)) ≤
      (2 / (48355719652839597 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1293 / 3200 : ℝ) - Real.pi * Real.exp (323 / 200 : ℝ) =
      -(Real.pi * Real.exp (323 / 200 : ℝ) - (1293 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (39538335807380319 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (39538335807380319 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1292_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (323 / 400 : ℝ) (1293 / 1600 : ℝ)) :
    (732303 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (375547 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1292_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1292_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1293_leftExp :
    (5034176713 / 1000000000 : ℝ) ≤ Real.exp (1293 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1293 / 800 : ℝ) (21036101611 / 20000000000 : ℝ)
    (5034176713 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1293_rightExp :
    Real.exp (647 / 400 : ℝ) ≤ (50404733687 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (647 / 400 : ℝ) (1051846167489 / 1000000000000 : ℝ)
    (50404733687 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1293_denomUpper :
    Real.exp (154310533517943391 / 10000000000000000 : ℝ) ≤ (628827221361259 / 125000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (154310533517943391 / 10000000000000000 : ℝ)
    (1619666748441 / 1000000000000 : ℝ) (628827221361259 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1293_denomLower :
    (1972206562261667 / 400000000 : ℝ) ≤ Real.exp (1926369286018387 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1926369286018387 / 125000000000000 : ℝ) (202331220259 /
    125000000000 : ℝ) (1972206562261667 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1293_product_lower :
    (1976916161018387 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (1293 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1293_leftExp
    (by norm_num : (0 : ℝ) ≤ (5034176713 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1293_product_upper :
    Real.pi * Real.exp (647 / 400 : ℝ) ≤ (158351158517943391 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1293_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1293_endpointLower :
    (3600379 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1293 / 1600 : ℝ) (647 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1976916161018387 / 125000000000000 : ℝ) (Real.pi * Real.exp (1293 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1293_product_lower
  have hD : Real.exp (Real.pi * Real.exp (647 / 400 : ℝ) - (1293 / 3200 : ℝ)) ≤
      (628827221361259 / 125000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1293_denomUpper
    linarith [hpThetaJensenCell1293_product_upper]
  have hi : (1 / (628827221361259 / 125000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (647 / 400 : ℝ) - (1293 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (628827221361259 / 125000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (628827221361259 / 125000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1293 / 3200 : ℝ) - Real.pi * Real.exp (647 / 400 : ℝ)) := by
    rw [show (1293 / 3200 : ℝ) - Real.pi * Real.exp (647 / 400 : ℝ) =
      -(Real.pi * Real.exp (647 / 400 : ℝ) - (1293 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1293 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1293 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1293_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (628827221361259 / 125000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1293_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1293 / 1600 : ℝ) (647 / 800 : ℝ) ≤ (738571 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (647 / 400 : ℝ)) (158351158517943391 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (647 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1293_product_upper
  have hD : (1972206562261667 / 400000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1293 / 800 : ℝ) - (647 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1293_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1293_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1293 / 800 : ℝ) - (647 / 1600 : ℝ)) ≤
      (1 / (1972206562261667 / 400000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1972206562261667 / 400000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((647 / 1600 : ℝ) - Real.pi * Real.exp (1293 / 800 : ℝ)) ≤
      (2 / (1972206562261667 / 400000000 : ℝ) : ℝ) := by
    rw [show (647 / 1600 : ℝ) - Real.pi * Real.exp (1293 / 800 : ℝ) =
      -(Real.pi * Real.exp (1293 / 800 : ℝ) - (647 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (158351158517943391 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (158351158517943391 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1293_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1293 / 1600 : ℝ) (647 / 800 : ℝ)) :
    (3600379 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (738571 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1293_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1293_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1294_leftExp :
    (12601183421 / 2500000000 : ℝ) ≤ Real.exp (647 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (647 / 400 : ℝ) (16435096367 / 15625000000 : ℝ)
    (12601183421 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1294_rightExp :
    Real.exp (259 / 160 : ℝ) ≤ (25233889499 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (259 / 160 : ℝ) (32871476751 / 31250000000 : ℝ)
    (25233889499 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1294_denomUpper :
    Real.exp (77252735612831907 / 5000000000000000 : ℝ) ≤ (51296455571425887 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (77252735612831907 / 5000000000000000 : ℝ) (1620653718167
    / 1000000000000 : ℝ) (51296455571425887 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1294_denomLower :
    (12568623178596467 / 2500000000 : ℝ) ≤ Real.exp (4822007284493279 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4822007284493279 / 312500000000000 : ℝ) (404908714867 /
    250000000000 : ℝ) (12568623178596467 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1294_product_lower :
    (4948472128243279 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (647 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1294_leftExp
    (by norm_num : (0 : ℝ) ≤ (12601183421 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1294_product_upper :
    Real.pi * Real.exp (259 / 160 : ℝ) ≤ (79274610612831907 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1294_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1294_endpointLower :
    (141607 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (647 / 800 : ℝ) (259 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4948472128243279 / 312500000000000 : ℝ) (Real.pi * Real.exp (647 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1294_product_lower
  have hD : Real.exp (Real.pi * Real.exp (259 / 160 : ℝ) - (647 / 1600 : ℝ)) ≤
      (51296455571425887 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1294_denomUpper
    linarith [hpThetaJensenCell1294_product_upper]
  have hi : (1 / (51296455571425887 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (259 / 160 : ℝ) - (647 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (51296455571425887 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (51296455571425887 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((647 / 1600 : ℝ) - Real.pi * Real.exp (259 / 160 : ℝ)) := by
    rw [show (647 / 1600 : ℝ) - Real.pi * Real.exp (259 / 160 : ℝ) =
      -(Real.pi * Real.exp (259 / 160 : ℝ) - (647 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (647 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (647 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1294_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (51296455571425887 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1294_endpointUpper :
    hpThetaJensenKernelEndpointUpper (647 / 800 : ℝ) (259 / 320 : ℝ) ≤ (726239 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (259 / 160 : ℝ)) (79274610612831907 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (259 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1294_product_upper
  have hD : (12568623178596467 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (647 / 400 : ℝ) - (259 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1294_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1294_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (647 / 400 : ℝ) - (259 / 640 : ℝ)) ≤
      (1 / (12568623178596467 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (12568623178596467 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((259 / 640 : ℝ) - Real.pi * Real.exp (647 / 400 : ℝ)) ≤
      (2 / (12568623178596467 / 2500000000 : ℝ) : ℝ) := by
    rw [show (259 / 640 : ℝ) - Real.pi * Real.exp (647 / 400 : ℝ) =
      -(Real.pi * Real.exp (647 / 400 : ℝ) - (259 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (79274610612831907 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (79274610612831907 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1294_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (647 / 800 : ℝ) (259 / 320 : ℝ)) :
    (141607 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (726239 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1294_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1294_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1295_leftExp :
    (12616944749 / 2500000000 : ℝ) ≤ Real.exp (259 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (259 / 160 : ℝ) (1051887256031 / 1000000000000 : ℝ)
    (12616944749 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1295_rightExp :
    Real.exp (81 / 50 : ℝ) ≤ (50530903167 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (81 / 50 : ℝ) (1051928346181 / 1000000000000 : ℝ)
    (50530903167 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1295_denomUpper :
    Real.exp (154700656673125031 / 10000000000000000 : ℝ) ≤ (2615376145868557 / 500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (154700656673125031 / 10000000000000000 : ℝ)
    (405410636193 / 250000000000 : ℝ) (2615376145868557 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1295_denomLower :
    (51264146549653157 / 10000000000 : ℝ) ≤ Real.exp (4828099085987551 / 312500000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (4828099085987551 / 312500000000000 : ℝ) (810310904729 /
    500000000000 : ℝ) (51264146549653157 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1295_product_lower :
    (4954661585987551 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (259 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1295_leftExp
    (by norm_num : (0 : ℝ) ≤ (12616944749 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1295_product_upper :
    Real.pi * Real.exp (81 / 50 : ℝ) ≤ (158747531673125031 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1295_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1295_endpointLower :
    (3480891 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (259 / 320 : ℝ) (81 / 100 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4954661585987551 / 312500000000000 : ℝ) (Real.pi * Real.exp (259 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1295_product_lower
  have hD : Real.exp (Real.pi * Real.exp (81 / 50 : ℝ) - (259 / 640 : ℝ)) ≤
      (2615376145868557 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1295_denomUpper
    linarith [hpThetaJensenCell1295_product_upper]
  have hi : (1 / (2615376145868557 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (81 / 50 : ℝ) - (259 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2615376145868557 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2615376145868557 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((259 / 640 : ℝ) - Real.pi * Real.exp (81 / 50 : ℝ)) := by
    rw [show (259 / 640 : ℝ) - Real.pi * Real.exp (81 / 50 : ℝ) =
      -(Real.pi * Real.exp (81 / 50 : ℝ) - (259 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (259 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (259 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1295_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2615376145868557 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1295_endpointUpper :
    hpThetaJensenKernelEndpointUpper (259 / 320 : ℝ) (81 / 100 : ℝ) ≤ (1785237 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (81 / 50 : ℝ)) (158747531673125031 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (81 / 100 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1295_product_upper
  have hD : (51264146549653157 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (259 / 160 : ℝ) - (81 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1295_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1295_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (259 / 160 : ℝ) - (81 / 200 : ℝ)) ≤
      (1 / (51264146549653157 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (51264146549653157 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((81 / 200 : ℝ) - Real.pi * Real.exp (259 / 160 : ℝ)) ≤
      (2 / (51264146549653157 / 10000000000 : ℝ) : ℝ) := by
    rw [show (81 / 200 : ℝ) - Real.pi * Real.exp (259 / 160 : ℝ) =
      -(Real.pi * Real.exp (259 / 160 : ℝ) - (81 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (158747531673125031 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (158747531673125031 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1295_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (259 / 320 : ℝ) (81 / 100 : ℝ)) :
    (3480891 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1785237 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1295_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1295_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1296_leftExp :
    (12632725791 / 2500000000 : ℝ) ≤ Real.exp (81 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (81 / 50 : ℝ) (52596417309 / 50000000000 : ℝ)
    (12632725791 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1296_rightExp :
    Real.exp (1297 / 800 : ℝ) ≤ (5059410629 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1297 / 800 : ℝ) (210393887587 / 200000000000 : ℝ)
    (5059410629 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1296_denomUpper :
    Real.exp (15489609016191997 / 1000000000000000 : ℝ) ≤ (53339841712754481 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (15489609016191997 / 1000000000000000 : ℝ) (32452664649 /
    20000000000 : ℝ) (53339841712754481 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1296_denomLower :
    (26137288365025523 / 5000000000 : ℝ) ≤ Real.exp (4834198629149909 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4834198629149909 / 312500000000000 : ℝ) (1621610616259 /
    1000000000000 : ℝ) (26137288365025523 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1296_product_lower :
    (4960858785399909 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (81 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1296_leftExp
    (by norm_num : (0 : ℝ) ≤ (12632725791 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1296_product_upper :
    Real.pi * Real.exp (1297 / 800 : ℝ) ≤ (15894609016191997 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1296_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1296_endpointLower :
    (1711257 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (81 / 100 : ℝ) (1297 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4960858785399909 / 312500000000000 : ℝ) (Real.pi * Real.exp (81 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell1296_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1297 / 800 : ℝ) - (81 / 200 : ℝ)) ≤
      (53339841712754481 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1296_denomUpper
    linarith [hpThetaJensenCell1296_product_upper]
  have hi : (1 / (53339841712754481 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1297 / 800 : ℝ) - (81 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (53339841712754481 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (53339841712754481 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((81 / 200 : ℝ) - Real.pi * Real.exp (1297 / 800 : ℝ)) := by
    rw [show (81 / 200 : ℝ) - Real.pi * Real.exp (1297 / 800 : ℝ) =
      -(Real.pi * Real.exp (1297 / 800 : ℝ) - (81 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (81 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (81 / 50 : ℝ)) := by
    have h := hpThetaJensenCell1296_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (53339841712754481 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1296_endpointUpper :
    hpThetaJensenKernelEndpointUpper (81 / 100 : ℝ) (1297 / 1600 : ℝ) ≤ (1755341 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1297 / 800 : ℝ)) (15894609016191997 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1297 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1296_product_upper
  have hD : (26137288365025523 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (81 / 50 : ℝ) - (1297 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1296_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1296_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (81 / 50 : ℝ) - (1297 / 3200 : ℝ)) ≤
      (1 / (26137288365025523 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (26137288365025523 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1297 / 3200 : ℝ) - Real.pi * Real.exp (81 / 50 : ℝ)) ≤
      (2 / (26137288365025523 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1297 / 3200 : ℝ) - Real.pi * Real.exp (81 / 50 : ℝ) =
      -(Real.pi * Real.exp (81 / 50 : ℝ) - (1297 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (15894609016191997 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (15894609016191997 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1296_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (81 / 100 : ℝ) (1297 / 1600 : ℝ)) :
    (1711257 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1755341 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1296_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1296_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1297_leftExp :
    (3162131643 / 625000000 : ℝ) ≤ Real.exp (1297 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1297 / 800 : ℝ) (525984718967 / 500000000000 : ℝ)
    (3162131643 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1297_rightExp :
    Real.exp (649 / 400 : ℝ) ≤ (10131477693 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (649 / 400 : ℝ) (1052010531293 / 1000000000000 : ℝ)
    (10131477693 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1297_denomUpper :
    Real.exp (31018354399984949 / 2000000000000000 : ℝ) ≤ (5439388475991947 / 1000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (31018354399984949 / 2000000000000000 : ℝ) (1623625785437
    / 1000000000000 : ℝ) (5439388475991947 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1297_denomLower :
    (26653122496839151 / 5000000000 : ℝ) ≤ Real.exp (1210076480949457 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1210076480949457 / 78125000000000 : ℝ) (1622601284127 /
    1000000000000 : ℝ) (26653122496839151 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1297_product_lower :
    (1241765934074457 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (1297 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1297_leftExp
    (by norm_num : (0 : ℝ) ≤ (3162131643 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1297_product_upper :
    Real.pi * Real.exp (649 / 400 : ℝ) ≤ (31828979399984949 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1297_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1297_endpointLower :
    (3365033 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1297 / 1600 : ℝ) (649 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1241765934074457 / 78125000000000 : ℝ) (Real.pi * Real.exp (1297 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1297_product_lower
  have hD : Real.exp (Real.pi * Real.exp (649 / 400 : ℝ) - (1297 / 3200 : ℝ)) ≤
      (5439388475991947 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1297_denomUpper
    linarith [hpThetaJensenCell1297_product_upper]
  have hi : (1 / (5439388475991947 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (649 / 400 : ℝ) - (1297 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5439388475991947 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5439388475991947 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1297 / 3200 : ℝ) - Real.pi * Real.exp (649 / 400 : ℝ)) := by
    rw [show (1297 / 3200 : ℝ) - Real.pi * Real.exp (649 / 400 : ℝ) =
      -(Real.pi * Real.exp (649 / 400 : ℝ) - (1297 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1297 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1297 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1297_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5439388475991947 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1297_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1297 / 1600 : ℝ) (649 / 800 : ℝ) ≤ (862951 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (649 / 400 : ℝ)) (31828979399984949 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (649 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1297_product_upper
  have hD : (26653122496839151 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1297 / 800 : ℝ) - (649 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1297_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1297_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1297 / 800 : ℝ) - (649 / 1600 : ℝ)) ≤
      (1 / (26653122496839151 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (26653122496839151 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((649 / 1600 : ℝ) - Real.pi * Real.exp (1297 / 800 : ℝ)) ≤
      (2 / (26653122496839151 / 5000000000 : ℝ) : ℝ) := by
    rw [show (649 / 1600 : ℝ) - Real.pi * Real.exp (1297 / 800 : ℝ) =
      -(Real.pi * Real.exp (1297 / 800 : ℝ) - (649 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (31828979399984949 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (31828979399984949 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1297_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1297 / 1600 : ℝ) (649 / 800 : ℝ)) :
    (3365033 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (862951 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1297_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1297_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1298_leftExp :
    (50657388463 / 10000000000 : ℝ) ≤ Real.exp (649 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (649 / 400 : ℝ) (263002632823 / 250000000000 : ℝ)
    (50657388463 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1298_rightExp :
    Real.exp (1299 / 800 : ℝ) ≤ (50720749793 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1299 / 800 : ℝ) (1052051626257 / 1000000000000 : ℝ)
    (50720749793 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1298_denomUpper :
    Real.exp (155287702504440249 / 10000000000000000 : ℝ) ≤ (55470135980622201 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (155287702504440249 / 10000000000000000 : ℝ) (64984808321
    / 40000000000 : ℝ) (55470135980622201 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1298_denomLower :
    (6794952974398931 / 1250000000 : ℝ) ≤ Real.exp (19385683917031637 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (19385683917031637 / 1250000000000000 : ℝ) (6494375269 /
    4000000000 : ℝ) (6794952974398931 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1298_product_lower :
    (19893105792031637 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (649 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1298_leftExp
    (by norm_num : (0 : ℝ) ≤ (50657388463 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1298_product_upper :
    Real.pi * Real.exp (1299 / 800 : ℝ) ≤ (159343952504440249 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1298_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1298_endpointLower :
    (3308433 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (649 / 800 : ℝ) (1299 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (19893105792031637 / 1250000000000000 : ℝ) (Real.pi * Real.exp (649 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1298_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1299 / 800 : ℝ) - (649 / 1600 : ℝ)) ≤
      (55470135980622201 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1298_denomUpper
    linarith [hpThetaJensenCell1298_product_upper]
  have hi : (1 / (55470135980622201 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1299 / 800 : ℝ) - (649 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (55470135980622201 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (55470135980622201 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((649 / 1600 : ℝ) - Real.pi * Real.exp (1299 / 800 : ℝ)) := by
    rw [show (649 / 1600 : ℝ) - Real.pi * Real.exp (1299 / 800 : ℝ) =
      -(Real.pi * Real.exp (1299 / 800 : ℝ) - (649 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (649 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (649 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1298_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (55470135980622201 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1298_endpointUpper :
    hpThetaJensenKernelEndpointUpper (649 / 800 : ℝ) (1299 / 1600 : ℝ) ≤ (3393829 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1299 / 800 : ℝ)) (159343952504440249 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1299 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1298_product_upper
  have hD : (6794952974398931 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (649 / 400 : ℝ) - (1299 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1298_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1298_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (649 / 400 : ℝ) - (1299 / 3200 : ℝ)) ≤
      (1 / (6794952974398931 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6794952974398931 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1299 / 3200 : ℝ) - Real.pi * Real.exp (649 / 400 : ℝ)) ≤
      (2 / (6794952974398931 / 1250000000 : ℝ) : ℝ) := by
    rw [show (1299 / 3200 : ℝ) - Real.pi * Real.exp (649 / 400 : ℝ) =
      -(Real.pi * Real.exp (649 / 400 : ℝ) - (1299 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (159343952504440249 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (159343952504440249 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1298_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (649 / 800 : ℝ) (1299 / 1600 : ℝ)) :
    (3308433 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3393829 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1298_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1298_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1299_leftExp :
    (50720749791 / 10000000000 : ℝ) ≤ Real.exp (1299 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1299 / 800 : ℝ) (65753226641 / 62500000000 : ℝ)
    (50720749791 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1299_rightExp :
    Real.exp (13 / 8 : ℝ) ≤ (25392095187 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (13 / 8 : ℝ) (1052092722827 / 1000000000000 : ℝ)
    (25392095187 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1299_denomUpper :
    Real.exp (77741940994812891 / 5000000000000000 : ℝ) ≤ (28284545312159781 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (77741940994812891 / 5000000000000000 : ℝ) (1625616504501
    / 1000000000000 : ℝ) (28284545312159781 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1299_denomLower :
    (55435196768761241 / 10000000000 : ℝ) ≤ Real.exp (19410175222175909 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (19410175222175909 / 1250000000000000 : ℝ) (1624588219937
    / 1000000000000 : ℝ) (55435196768761241 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1299_product_lower :
    (19917987722175909 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1299 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1299_leftExp
    (by norm_num : (0 : ℝ) ≤ (50720749791 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1299_product_upper :
    Real.pi * Real.exp (13 / 8 : ℝ) ≤ (79771628494812891 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1299_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1299_endpointLower :
    (650541 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1299 / 1600 : ℝ) (13 / 16 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (19917987722175909 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1299 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1299_product_lower
  have hD : Real.exp (Real.pi * Real.exp (13 / 8 : ℝ) - (1299 / 3200 : ℝ)) ≤
      (28284545312159781 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1299_denomUpper
    linarith [hpThetaJensenCell1299_product_upper]
  have hi : (1 / (28284545312159781 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (13 / 8 : ℝ) - (1299 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (28284545312159781 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (28284545312159781 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1299 / 3200 : ℝ) - Real.pi * Real.exp (13 / 8 : ℝ)) := by
    rw [show (1299 / 3200 : ℝ) - Real.pi * Real.exp (13 / 8 : ℝ) =
      -(Real.pi * Real.exp (13 / 8 : ℝ) - (1299 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1299 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1299 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1299_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (28284545312159781 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1299_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1299 / 1600 : ℝ) (13 / 16 : ℝ) ≤ (667349 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (13 / 8 : ℝ)) (79771628494812891 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (13 / 16 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1299_product_upper
  have hD : (55435196768761241 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1299 / 800 : ℝ) - (13 / 32 : ℝ)) := by
    apply le_trans hpThetaJensenCell1299_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1299_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1299 / 800 : ℝ) - (13 / 32 : ℝ)) ≤
      (1 / (55435196768761241 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (55435196768761241 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((13 / 32 : ℝ) - Real.pi * Real.exp (1299 / 800 : ℝ)) ≤
      (2 / (55435196768761241 / 10000000000 : ℝ) : ℝ) := by
    rw [show (13 / 32 : ℝ) - Real.pi * Real.exp (1299 / 800 : ℝ) =
      -(Real.pi * Real.exp (1299 / 800 : ℝ) - (13 / 32 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (79771628494812891 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (79771628494812891 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1299_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1299 / 1600 : ℝ) (13 / 16 : ℝ)) :
    (650541 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (667349 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1299_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1299_endpointUpper

def hpThetaJensenCellsBatch064Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (4472733 / 10000000000 : ℝ)
  | 1 => (4399357 / 10000000000 : ℝ)
  | 2 => (2163539 / 5000000000 : ℝ)
  | 3 => (4255883 / 10000000000 : ℝ)
  | 4 => (837151 / 2000000000 : ℝ)
  | 5 => (2058341 / 5000000000 : ℝ)
  | 6 => (506081 / 1250000000 : ℝ)
  | 7 => (3981641 / 10000000000 : ℝ)
  | 8 => (1957823 / 5000000000 : ℝ)
  | 9 => (3850649 / 10000000000 : ℝ)
  | 10 => (3786637 / 10000000000 : ℝ)
  | 11 => (3723597 / 10000000000 : ℝ)
  | 12 => (732303 / 2000000000 : ℝ)
  | 13 => (3600379 / 10000000000 : ℝ)
  | 14 => (141607 / 400000000 : ℝ)
  | 15 => (3480891 / 10000000000 : ℝ)
  | 16 => (1711257 / 5000000000 : ℝ)
  | 17 => (3365033 / 10000000000 : ℝ)
  | 18 => (3308433 / 10000000000 : ℝ)
  | 19 => (650541 / 2000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch064Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1146541 / 2500000000 : ℝ)
  | 1 => (1127759 / 2500000000 : ℝ)
  | 2 => (443703 / 1000000000 : ℝ)
  | 3 => (4364131 / 10000000000 : ℝ)
  | 4 => (1073081 / 2500000000 : ℝ)
  | 5 => (844319 / 2000000000 : ℝ)
  | 6 => (4151929 / 10000000000 : ℝ)
  | 7 => (4083311 / 10000000000 : ℝ)
  | 8 => (4015729 / 10000000000 : ℝ)
  | 9 => (3949167 / 10000000000 : ℝ)
  | 10 => (970903 / 2500000000 : ℝ)
  | 11 => (3819051 / 10000000000 : ℝ)
  | 12 => (375547 / 1000000000 : ℝ)
  | 13 => (738571 / 2000000000 : ℝ)
  | 14 => (726239 / 2000000000 : ℝ)
  | 15 => (1785237 / 5000000000 : ℝ)
  | 16 => (1755341 / 5000000000 : ℝ)
  | 17 => (862951 / 2500000000 : ℝ)
  | 18 => (3393829 / 10000000000 : ℝ)
  | 19 => (667349 / 2000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch064_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1280 : ℝ) + (j.val : ℝ)) / 1600)
      (((1280 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch064Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch064Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1280_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1281_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1282_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1283_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1284_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1285_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1286_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1287_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1288_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1289_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1290_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1291_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1292_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1293_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1294_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1295_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1296_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1297_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1298_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1299_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper] at h ⊢
    exact h

end HodgeProofHP
