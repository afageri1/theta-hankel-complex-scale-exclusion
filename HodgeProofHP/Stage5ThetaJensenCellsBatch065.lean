import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1300_leftExp :
    (50784190371 / 10000000000 : ℝ) ≤ Real.exp (13 / 8 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (13 / 8 : ℝ) (526046361413 / 500000000000 : ℝ)
    (50784190371 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1300_rightExp :
    Real.exp (1301 / 800 : ℝ) ≤ (25423855151 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1301 / 800 : ℝ) (1052133821001 / 1000000000000 : ℝ)
    (25423855151 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1300_denomUpper :
    Real.exp (77840155375395543 / 5000000000000000 : ℝ) ≤ (5769125545430041 / 1000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (77840155375395543 / 5000000000000000 : ℝ) (1626614679067
    / 1000000000000 : ℝ) (5769125545430041 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1300_denomLower :
    (3533341177041493 / 625000000 : ℝ) ≤ Real.exp (19434697649501329 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (19434697649501329 / 1250000000000000 : ℝ) (812792248229
    / 500000000000 : ℝ) (3533341177041493 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1300_product_lower :
    (19942900774501329 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (13 / 8 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1300_leftExp
    (by norm_num : (0 : ℝ) ≤ (50784190371 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1300_product_upper :
    Real.pi * Real.exp (1301 / 800 : ℝ) ≤ (79871405375395543 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1300_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1300_endpointLower :
    (1598917 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (13 / 16 : ℝ) (1301 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (19942900774501329 / 1250000000000000 : ℝ) (Real.pi * Real.exp (13 / 8 : ℝ))
    (by norm_num) hpThetaJensenCell1300_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1301 / 800 : ℝ) - (13 / 32 : ℝ)) ≤
      (5769125545430041 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1300_denomUpper
    linarith [hpThetaJensenCell1300_product_upper]
  have hi : (1 / (5769125545430041 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1301 / 800 : ℝ) - (13 / 32 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5769125545430041 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5769125545430041 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((13 / 32 : ℝ) - Real.pi * Real.exp (1301 / 800 : ℝ)) := by
    rw [show (13 / 32 : ℝ) - Real.pi * Real.exp (1301 / 800 : ℝ) =
      -(Real.pi * Real.exp (1301 / 800 : ℝ) - (13 / 32 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (13 / 8 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (13 / 8 : ℝ)) := by
    have h := hpThetaJensenCell1300_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5769125545430041 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1300_endpointUpper :
    hpThetaJensenKernelEndpointUpper (13 / 16 : ℝ) (1301 / 1600 : ℝ) ≤ (1640269 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1301 / 800 : ℝ)) (79871405375395543 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1301 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1300_product_upper
  have hD : (3533341177041493 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (13 / 8 : ℝ) - (1301 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1300_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1300_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (13 / 8 : ℝ) - (1301 / 3200 : ℝ)) ≤
      (1 / (3533341177041493 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3533341177041493 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1301 / 3200 : ℝ) - Real.pi * Real.exp (13 / 8 : ℝ)) ≤
      (2 / (3533341177041493 / 625000000 : ℝ) : ℝ) := by
    rw [show (1301 / 3200 : ℝ) - Real.pi * Real.exp (13 / 8 : ℝ) =
      -(Real.pi * Real.exp (13 / 8 : ℝ) - (1301 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (79871405375395543 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (79871405375395543 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1300_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (13 / 16 : ℝ) (1301 / 1600 : ℝ)) :
    (1598917 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1640269 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1300_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1300_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1301_leftExp :
    (508477103 / 100000000 : ℝ) ≤ Real.exp (1301 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1301 / 800 : ℝ) (1052133821 / 1000000000 : ℝ) (508477103
    / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1301_rightExp :
    Real.exp (651 / 400 : ℝ) ≤ (50911309681 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (651 / 400 : ℝ) (1052174920781 / 1000000000000 : ℝ)
    (50911309681 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1301_denomUpper :
    Real.exp (155876989114661833 / 10000000000000000 : ℝ) ≤ (1176742986334717 / 200000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (155876989114661833 / 10000000000000000 : ℝ)
    (813807368047 / 500000000000 : ℝ) (1176742986334717 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1301_denomLower :
    (1441372912128887 / 250000000 : ℝ) ≤ Real.exp (194592512370997 / 12500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (194592512370997 / 12500000000000 : ℝ) (203322831383 /
    125000000000 : ℝ) (1441372912128887 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1301_product_lower :
    (199678449870997 / 12500000000000 : ℝ) ≤ Real.pi * Real.exp (1301 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1301_leftExp
    (by norm_num : (0 : ℝ) ≤ (508477103 / 100000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1301_product_upper :
    Real.pi * Real.exp (651 / 400 : ℝ) ≤ (159942614114661833 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1301_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1301_endpointLower :
    (314381 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1301 / 1600 : ℝ) (651 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (199678449870997 / 12500000000000 : ℝ) (Real.pi * Real.exp (1301 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1301_product_lower
  have hD : Real.exp (Real.pi * Real.exp (651 / 400 : ℝ) - (1301 / 3200 : ℝ)) ≤
      (1176742986334717 / 200000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1301_denomUpper
    linarith [hpThetaJensenCell1301_product_upper]
  have hi : (1 / (1176742986334717 / 200000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (651 / 400 : ℝ) - (1301 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1176742986334717 / 200000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1176742986334717 / 200000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1301 / 3200 : ℝ) - Real.pi * Real.exp (651 / 400 : ℝ)) := by
    rw [show (1301 / 3200 : ℝ) - Real.pi * Real.exp (651 / 400 : ℝ) =
      -(Real.pi * Real.exp (651 / 400 : ℝ) - (1301 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1301 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1301 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1301_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1176742986334717 / 200000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1301_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1301 / 1600 : ℝ) (651 / 800 : ℝ) ≤ (3225197 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (651 / 400 : ℝ)) (159942614114661833 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (651 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1301_product_upper
  have hD : (1441372912128887 / 250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1301 / 800 : ℝ) - (651 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1301_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1301_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1301 / 800 : ℝ) - (651 / 1600 : ℝ)) ≤
      (1 / (1441372912128887 / 250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1441372912128887 / 250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((651 / 1600 : ℝ) - Real.pi * Real.exp (1301 / 800 : ℝ)) ≤
      (2 / (1441372912128887 / 250000000 : ℝ) : ℝ) := by
    rw [show (651 / 1600 : ℝ) - Real.pi * Real.exp (1301 / 800 : ℝ) =
      -(Real.pi * Real.exp (1301 / 800 : ℝ) - (651 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (159942614114661833 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (159942614114661833 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1301_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1301 / 1600 : ℝ) (651 / 800 : ℝ)) :
    (314381 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3225197 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1301_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1301_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1302_leftExp :
    (50911309679 / 10000000000 : ℝ) ≤ Real.exp (651 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (651 / 400 : ℝ) (52608746039 / 50000000000 : ℝ)
    (50911309679 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1302_rightExp :
    Real.exp (1303 / 800 : ℝ) ≤ (5097498861 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1303 / 800 : ℝ) (1052216022167 / 1000000000000 : ℝ)
    (5097498861 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1302_denomUpper :
    Real.exp (15607391739225573 / 1000000000000000 : ℝ) ≤ (1875228223960373 / 312500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (15607391739225573 / 1000000000000000 : ℝ) (1628616679881
    / 1000000000000 : ℝ) (1875228223960373 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1302_denomLower :
    (58800088189543057 / 10000000000 : ℝ) ≤ Real.exp (19483836024633621 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (19483836024633621 / 1250000000000000 : ℝ) (406895672019
    / 250000000000 : ℝ) (58800088189543057 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1302_product_lower :
    (19992820399633621 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (651 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1302_leftExp
    (by norm_num : (0 : ℝ) ≤ (50911309679 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1302_product_upper :
    Real.pi * Real.exp (1303 / 800 : ℝ) ≤ (16014266739225573 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1302_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1302_endpointLower :
    (3090621 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (651 / 800 : ℝ) (1303 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (19992820399633621 / 1250000000000000 : ℝ) (Real.pi * Real.exp (651 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1302_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1303 / 800 : ℝ) - (651 / 1600 : ℝ)) ≤
      (1875228223960373 / 312500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1302_denomUpper
    linarith [hpThetaJensenCell1302_product_upper]
  have hi : (1 / (1875228223960373 / 312500000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1303 / 800 : ℝ) - (651 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1875228223960373 / 312500000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1875228223960373 / 312500000 : ℝ) : ℝ) ≤
      2 * Real.exp ((651 / 1600 : ℝ) - Real.pi * Real.exp (1303 / 800 : ℝ)) := by
    rw [show (651 / 1600 : ℝ) - Real.pi * Real.exp (1303 / 800 : ℝ) =
      -(Real.pi * Real.exp (1303 / 800 : ℝ) - (651 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (651 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (651 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1302_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1875228223960373 / 312500000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1302_endpointUpper :
    hpThetaJensenKernelEndpointUpper (651 / 800 : ℝ) (1303 / 1600 : ℝ) ≤ (317071 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1303 / 800 : ℝ)) (16014266739225573 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1303 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1302_product_upper
  have hD : (58800088189543057 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (651 / 400 : ℝ) - (1303 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1302_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1302_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (651 / 400 : ℝ) - (1303 / 3200 : ℝ)) ≤
      (1 / (58800088189543057 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (58800088189543057 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1303 / 3200 : ℝ) - Real.pi * Real.exp (651 / 400 : ℝ)) ≤
      (2 / (58800088189543057 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1303 / 3200 : ℝ) - Real.pi * Real.exp (651 / 400 : ℝ) =
      -(Real.pi * Real.exp (651 / 400 : ℝ) - (1303 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (16014266739225573 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (16014266739225573 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1302_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (651 / 800 : ℝ) (1303 / 1600 : ℝ)) :
    (3090621 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (317071 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1302_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1302_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1303_leftExp :
    (796484197 / 156250000 : ℝ) ≤ Real.exp (1303 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1303 / 800 : ℝ) (526108011083 / 500000000000 : ℝ)
    (796484197 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1303_rightExp :
    Real.exp (163 / 100 : ℝ) ≤ (25519373593 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (163 / 100 : ℝ) (526128562579 / 500000000000 : ℝ)
    (25519373593 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1303_denomUpper :
    Real.exp (78135547944153649 / 5000000000000000 : ℝ) ≤ (15300565106155567 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (78135547944153649 / 5000000000000000 : ℝ) (1629620514709
    / 1000000000000 : ℝ) (15300565106155567 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1303_denomLower :
    (59969504586194299 / 10000000000 : ℝ) ≤ Real.exp (304819563302703 / 19531250000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (304819563302703 / 19531250000000 : ℝ) (1628584611811 /
    1000000000000 : ℝ) (59969504586194299 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1303_product_lower :
    (312778547677703 / 19531250000000 : ℝ) ≤ Real.pi * Real.exp (1303 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1303_leftExp
    (by norm_num : (0 : ℝ) ≤ (796484197 / 156250000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1303_product_upper :
    Real.pi * Real.exp (163 / 100 : ℝ) ≤ (80171485444153649 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1303_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1303_endpointLower :
    (189891 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (1303 / 1600 : ℝ) (163 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (312778547677703 / 19531250000000 : ℝ) (Real.pi * Real.exp (1303 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1303_product_lower
  have hD : Real.exp (Real.pi * Real.exp (163 / 100 : ℝ) - (1303 / 3200 : ℝ)) ≤
      (15300565106155567 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1303_denomUpper
    linarith [hpThetaJensenCell1303_product_upper]
  have hi : (1 / (15300565106155567 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (163 / 100 : ℝ) - (1303 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (15300565106155567 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (15300565106155567 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1303 / 3200 : ℝ) - Real.pi * Real.exp (163 / 100 : ℝ)) := by
    rw [show (1303 / 3200 : ℝ) - Real.pi * Real.exp (163 / 100 : ℝ) =
      -(Real.pi * Real.exp (163 / 100 : ℝ) - (1303 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1303 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1303 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1303_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (15300565106155567 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1303_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1303 / 1600 : ℝ) (163 / 200 : ℝ) ≤ (389633 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (163 / 100 : ℝ)) (80171485444153649 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (163 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1303_product_upper
  have hD : (59969504586194299 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1303 / 800 : ℝ) - (163 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1303_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1303_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1303 / 800 : ℝ) - (163 / 400 : ℝ)) ≤
      (1 / (59969504586194299 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (59969504586194299 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((163 / 400 : ℝ) - Real.pi * Real.exp (1303 / 800 : ℝ)) ≤
      (2 / (59969504586194299 / 10000000000 : ℝ) : ℝ) := by
    rw [show (163 / 400 : ℝ) - Real.pi * Real.exp (1303 / 800 : ℝ) =
      -(Real.pi * Real.exp (1303 / 800 : ℝ) - (163 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (80171485444153649 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (80171485444153649 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1303_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1303 / 1600 : ℝ) (163 / 200 : ℝ)) :
    (189891 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (389633 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1303_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1303_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1304_leftExp :
    (3189921699 / 625000000 : ℝ) ≤ Real.exp (163 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (163 / 100 : ℝ) (1052257125157 / 1000000000000 : ℝ)
    (3189921699 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1304_rightExp :
    Real.exp (261 / 160 : ℝ) ≤ (51102585511 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (261 / 160 : ℝ) (210459645951 / 200000000000 : ℝ)
    (51102585511 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1304_denomUpper :
    Real.exp (156468524923259023 / 10000000000000000 : ℝ) ≤ (31211288704090973 / 5000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (156468524923259023 / 10000000000000000 : ℝ)
    (326125248989 / 200000000000 : ℝ) (31211288704090973 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1304_denomLower :
    (611637087492127 / 100000000 : ℝ) ≤ Real.exp (1220818709713101 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1220818709713101 / 78125000000000 : ℝ) (1629588426547 /
    1000000000000 : ℝ) (611637087492127 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1304_product_lower :
    (1252679061275601 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (163 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1304_leftExp
    (by norm_num : (0 : ℝ) ≤ (3189921699 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1304_product_upper :
    Real.pi * Real.exp (261 / 160 : ℝ) ≤ (160543524923259023 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1304_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1304_endpointLower :
    (1493351 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (163 / 200 : ℝ) (261 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1252679061275601 / 78125000000000 : ℝ) (Real.pi * Real.exp (163 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1304_product_lower
  have hD : Real.exp (Real.pi * Real.exp (261 / 160 : ℝ) - (163 / 400 : ℝ)) ≤
      (31211288704090973 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1304_denomUpper
    linarith [hpThetaJensenCell1304_product_upper]
  have hi : (1 / (31211288704090973 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (261 / 160 : ℝ) - (163 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (31211288704090973 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (31211288704090973 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((163 / 400 : ℝ) - Real.pi * Real.exp (261 / 160 : ℝ)) := by
    rw [show (163 / 400 : ℝ) - Real.pi * Real.exp (261 / 160 : ℝ) =
      -(Real.pi * Real.exp (261 / 160 : ℝ) - (163 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (163 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (163 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1304_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (31211288704090973 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1304_endpointUpper :
    hpThetaJensenKernelEndpointUpper (163 / 200 : ℝ) (261 / 320 : ℝ) ≤ (12257 / 40000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (261 / 160 : ℝ)) (160543524923259023 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (261 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1304_product_upper
  have hD : (611637087492127 / 100000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (163 / 100 : ℝ) - (261 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1304_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1304_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (163 / 100 : ℝ) - (261 / 640 : ℝ)) ≤
      (1 / (611637087492127 / 100000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (611637087492127 / 100000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((261 / 640 : ℝ) - Real.pi * Real.exp (163 / 100 : ℝ)) ≤
      (2 / (611637087492127 / 100000000 : ℝ) : ℝ) := by
    rw [show (261 / 640 : ℝ) - Real.pi * Real.exp (163 / 100 : ℝ) =
      -(Real.pi * Real.exp (163 / 100 : ℝ) - (261 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (160543524923259023 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (160543524923259023 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1304_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (163 / 200 : ℝ) (261 / 320 : ℝ)) :
    (1493351 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (12257 / 40000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1304_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1304_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1305_leftExp :
    (51102585509 / 10000000000 : ℝ) ≤ Real.exp (261 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (261 / 160 : ℝ) (526149114877 / 500000000000 : ℝ)
    (51102585509 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1305_rightExp :
    Real.exp (653 / 400 : ℝ) ≤ (51166503683 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (653 / 400 : ℝ) (1052339335957 / 1000000000000 : ℝ)
    (51166503683 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1305_denomUpper :
    Real.exp (156666204804987019 / 10000000000000000 : ℝ) ≤ (63668823485155379 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (156666204804987019 / 10000000000000000 : ℝ)
    (203954234363 / 125000000000 : ℝ) (63668823485155379 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1305_denomLower :
    (31191628325154093 / 5000000000 : ℝ) ≤ Real.exp (19557777976798791 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (19557777976798791 / 1250000000000000 : ℝ) (326118827331
    / 200000000000 : ℝ) (31191628325154093 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1305_product_lower :
    (20067934226798791 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (261 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1305_leftExp
    (by norm_num : (0 : ℝ) ≤ (51102585509 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1305_product_upper :
    Real.pi * Real.exp (653 / 400 : ℝ) ≤ (160744329804987019 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1305_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1305_endpointLower :
    (2935949 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (261 / 320 : ℝ) (653 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (20067934226798791 / 1250000000000000 : ℝ) (Real.pi * Real.exp (261 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1305_product_lower
  have hD : Real.exp (Real.pi * Real.exp (653 / 400 : ℝ) - (261 / 640 : ℝ)) ≤
      (63668823485155379 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1305_denomUpper
    linarith [hpThetaJensenCell1305_product_upper]
  have hi : (1 / (63668823485155379 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (653 / 400 : ℝ) - (261 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (63668823485155379 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (63668823485155379 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((261 / 640 : ℝ) - Real.pi * Real.exp (653 / 400 : ℝ)) := by
    rw [show (261 / 640 : ℝ) - Real.pi * Real.exp (653 / 400 : ℝ) =
      -(Real.pi * Real.exp (653 / 400 : ℝ) - (261 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (261 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (261 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1305_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (63668823485155379 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1305_endpointUpper :
    hpThetaJensenKernelEndpointUpper (261 / 320 : ℝ) (653 / 800 : ℝ) ≤ (1506127 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (653 / 400 : ℝ)) (160744329804987019 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (653 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1305_product_upper
  have hD : (31191628325154093 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (261 / 160 : ℝ) - (653 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1305_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1305_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (261 / 160 : ℝ) - (653 / 1600 : ℝ)) ≤
      (1 / (31191628325154093 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (31191628325154093 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((653 / 1600 : ℝ) - Real.pi * Real.exp (261 / 160 : ℝ)) ≤
      (2 / (31191628325154093 / 5000000000 : ℝ) : ℝ) := by
    rw [show (653 / 1600 : ℝ) - Real.pi * Real.exp (261 / 160 : ℝ) =
      -(Real.pi * Real.exp (261 / 160 : ℝ) - (653 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (160744329804987019 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (160744329804987019 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1305_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (261 / 320 : ℝ) (653 / 800 : ℝ)) :
    (2935949 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1506127 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1305_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1305_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1306_leftExp :
    (51166503681 / 10000000000 : ℝ) ≤ Real.exp (653 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (653 / 400 : ℝ) (263084833989 / 250000000000 : ℝ)
    (51166503681 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1306_rightExp :
    Real.exp (1307 / 800 : ℝ) ≤ (12807625451 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1307 / 800 : ℝ) (526190221883 / 500000000000 : ℝ)
    (12807625451 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1306_denomUpper :
    Real.exp (39216033963483443 / 2500000000000000 : ℝ) ≤ (8117697693969673 / 1250000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (39216033963483443 / 2500000000000000 : ℝ) (102040213061
    / 62500000000 : ℝ) (8117697693969673 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1306_denomLower :
    (12725743458913773 / 2000000000 : ℝ) ≤ Real.exp (19582487954025019 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (19582487954025019 / 1250000000000000 : ℝ) (1631601746447
    / 1000000000000 : ℝ) (12725743458913773 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1306_product_lower :
    (20093034829025019 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (653 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1306_leftExp
    (by norm_num : (0 : ℝ) ≤ (51166503681 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1306_product_upper :
    Real.pi * Real.exp (1307 / 800 : ℝ) ≤ (40236346463483443 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1306_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1306_endpointLower :
    (577197 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (653 / 800 : ℝ) (1307 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (20093034829025019 / 1250000000000000 : ℝ) (Real.pi * Real.exp (653 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1306_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1307 / 800 : ℝ) - (653 / 1600 : ℝ)) ≤
      (8117697693969673 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1306_denomUpper
    linarith [hpThetaJensenCell1306_product_upper]
  have hi : (1 / (8117697693969673 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1307 / 800 : ℝ) - (653 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (8117697693969673 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (8117697693969673 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((653 / 1600 : ℝ) - Real.pi * Real.exp (1307 / 800 : ℝ)) := by
    rw [show (653 / 1600 : ℝ) - Real.pi * Real.exp (1307 / 800 : ℝ) =
      -(Real.pi * Real.exp (1307 / 800 : ℝ) - (653 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (653 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (653 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1306_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (8117697693969673 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1306_endpointUpper :
    hpThetaJensenKernelEndpointUpper (653 / 800 : ℝ) (1307 / 1600 : ℝ) ≤ (1480533 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1307 / 800 : ℝ)) (40236346463483443 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1307 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1306_product_upper
  have hD : (12725743458913773 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (653 / 400 : ℝ) - (1307 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1306_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1306_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (653 / 400 : ℝ) - (1307 / 3200 : ℝ)) ≤
      (1 / (12725743458913773 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (12725743458913773 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1307 / 3200 : ℝ) - Real.pi * Real.exp (653 / 400 : ℝ)) ≤
      (2 / (12725743458913773 / 2000000000 : ℝ) : ℝ) := by
    rw [show (1307 / 3200 : ℝ) - Real.pi * Real.exp (653 / 400 : ℝ) =
      -(Real.pi * Real.exp (653 / 400 : ℝ) - (1307 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (40236346463483443 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (40236346463483443 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1306_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (653 / 800 : ℝ) (1307 / 1600 : ℝ)) :
    (577197 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1480533 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1306_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1306_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1307_leftExp :
    (25615250901 / 5000000000 : ℝ) ≤ Real.exp (1307 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1307 / 800 : ℝ) (210476088753 / 200000000000 : ℝ)
    (25615250901 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1307_rightExp :
    Real.exp (327 / 200 : ℝ) ≤ (12823644993 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (327 / 200 : ℝ) (52621077659 / 50000000000 : ℝ)
    (12823644993 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1307_denomUpper :
    Real.exp (39265579594493849 / 2500000000000000 : ℝ) ≤ (16560362051424643 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (39265579594493849 / 2500000000000000 : ℝ) (1633654851497
    / 1000000000000 : ℝ) (16560362051424643 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1307_denomLower :
    (64900673211830441 / 10000000000 : ℝ) ≤ Real.exp (9803614663571799 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (9803614663571799 / 625000000000000 : ℝ) (816305630157 /
    500000000000 : ℝ) (64900673211830441 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1307_product_lower :
    (10059083413571799 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1307 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1307_leftExp
    (by norm_num : (0 : ℝ) ≤ (25615250901 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1307_product_upper :
    Real.pi * Real.exp (327 / 200 : ℝ) ≤ (40286673344493849 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1307_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1307_endpointLower :
    (1773 / 6250000 : ℝ) ≤ hpThetaTraceEndpointLower (1307 / 1600 : ℝ) (327 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10059083413571799 / 625000000000000 : ℝ) (Real.pi * Real.exp (1307 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1307_product_lower
  have hD : Real.exp (Real.pi * Real.exp (327 / 200 : ℝ) - (1307 / 3200 : ℝ)) ≤
      (16560362051424643 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1307_denomUpper
    linarith [hpThetaJensenCell1307_product_upper]
  have hi : (1 / (16560362051424643 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (327 / 200 : ℝ) - (1307 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (16560362051424643 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (16560362051424643 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1307 / 3200 : ℝ) - Real.pi * Real.exp (327 / 200 : ℝ)) := by
    rw [show (1307 / 3200 : ℝ) - Real.pi * Real.exp (327 / 200 : ℝ) =
      -(Real.pi * Real.exp (327 / 200 : ℝ) - (1307 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1307 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1307 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1307_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (16560362051424643 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1307_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1307 / 1600 : ℝ) (327 / 400 : ℝ) ≤ (2910673 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (327 / 200 : ℝ)) (40286673344493849 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (327 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1307_product_upper
  have hD : (64900673211830441 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1307 / 800 : ℝ) - (327 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1307_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1307_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1307 / 800 : ℝ) - (327 / 800 : ℝ)) ≤
      (1 / (64900673211830441 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (64900673211830441 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((327 / 800 : ℝ) - Real.pi * Real.exp (1307 / 800 : ℝ)) ≤
      (2 / (64900673211830441 / 10000000000 : ℝ) : ℝ) := by
    rw [show (327 / 800 : ℝ) - Real.pi * Real.exp (1307 / 800 : ℝ) =
      -(Real.pi * Real.exp (1307 / 800 : ℝ) - (327 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (40286673344493849 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (40286673344493849 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1307_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1307 / 1600 : ℝ) (327 / 400 : ℝ)) :
    (1773 / 6250000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2910673 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1307_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1307_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1308_leftExp :
    (5129457997 / 1000000000 : ℝ) ≤ Real.exp (327 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (327 / 200 : ℝ) (1052421553179 / 1000000000000 : ℝ)
    (5129457997 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1308_rightExp :
    Real.exp (1309 / 800 : ℝ) ≤ (25679369143 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1309 / 800 : ℝ) (1052462664199 / 1000000000000 : ℝ)
    (25679369143 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1308_denomUpper :
    Real.exp (78630376344064799 / 5000000000000000 : ℝ) ≤ (13513806836252679 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (78630376344064799 / 5000000000000000 : ℝ) (817334103413
    / 500000000000 : ℝ) (13513806836252679 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1308_denomLower :
    (16549930155571851 / 2500000000 : ℝ) ≤ Real.exp (1963200213463903 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1963200213463903 / 125000000000000 : ℝ) (1633622682591 /
    1000000000000 : ℝ) (16549930155571851 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1308_product_lower :
    (2014333025963903 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (327 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1308_leftExp
    (by norm_num : (0 : ℝ) ≤ (5129457997 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1308_product_upper :
    Real.pi * Real.exp (1309 / 800 : ℝ) ≤ (80674126344064799 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1308_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1308_endpointLower :
    (1394191 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (327 / 400 : ℝ) (1309 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2014333025963903 / 125000000000000 : ℝ) (Real.pi * Real.exp (327 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1308_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1309 / 800 : ℝ) - (327 / 800 : ℝ)) ≤
      (13513806836252679 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1308_denomUpper
    linarith [hpThetaJensenCell1308_product_upper]
  have hi : (1 / (13513806836252679 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1309 / 800 : ℝ) - (327 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (13513806836252679 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (13513806836252679 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((327 / 800 : ℝ) - Real.pi * Real.exp (1309 / 800 : ℝ)) := by
    rw [show (327 / 800 : ℝ) - Real.pi * Real.exp (1309 / 800 : ℝ) =
      -(Real.pi * Real.exp (1309 / 800 : ℝ) - (327 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (327 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (327 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1308_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (13513806836252679 / 2000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1308_endpointUpper :
    hpThetaJensenKernelEndpointUpper (327 / 400 : ℝ) (1309 / 1600 : ℝ) ≤ (1430533 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1309 / 800 : ℝ)) (80674126344064799 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1309 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1308_product_upper
  have hD : (16549930155571851 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (327 / 200 : ℝ) - (1309 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1308_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1308_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (327 / 200 : ℝ) - (1309 / 3200 : ℝ)) ≤
      (1 / (16549930155571851 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (16549930155571851 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1309 / 3200 : ℝ) - Real.pi * Real.exp (327 / 200 : ℝ)) ≤
      (2 / (16549930155571851 / 2500000000 : ℝ) : ℝ) := by
    rw [show (1309 / 3200 : ℝ) - Real.pi * Real.exp (327 / 200 : ℝ) =
      -(Real.pi * Real.exp (327 / 200 : ℝ) - (1309 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (80674126344064799 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (80674126344064799 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1308_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (327 / 400 : ℝ) (1309 / 1600 : ℝ)) :
    (1394191 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1430533 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1308_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1308_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1309_leftExp :
    (12839684571 / 2500000000 : ℝ) ≤ Real.exp (1309 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1309 / 800 : ℝ) (526231332099 / 500000000000 : ℝ)
    (12839684571 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1309_rightExp :
    Real.exp (131 / 80 : ℝ) ≤ (1028459537 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (131 / 80 : ℝ) (42100151073 / 40000000000 : ℝ)
    (1028459537 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1309_denomUpper :
    Real.exp (3149188782222441 / 200000000000000 : ℝ) ≤ (1723124119912099 / 250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3149188782222441 / 200000000000000 : ℝ) (204460434927 /
    125000000000 : ℝ) (1723124119912099 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1309_denomLower :
    (67526469876339823 / 10000000000 : ℝ) ≤ Real.exp (4914201603847129 / 312500000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (4914201603847129 / 312500000000000 : ℝ) (817318008819 /
    500000000000 : ℝ) (67526469876339823 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1309_product_lower :
    (5042131291347129 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (1309 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1309_leftExp
    (by norm_num : (0 : ℝ) ≤ (12839684571 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1309_product_upper :
    Real.pi * Real.exp (131 / 80 : ℝ) ≤ (3231001282222441 / 200000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1309_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1309_endpointLower :
    (2740721 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1309 / 1600 : ℝ) (131 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5042131291347129 / 312500000000000 : ℝ) (Real.pi * Real.exp (1309 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1309_product_lower
  have hD : Real.exp (Real.pi * Real.exp (131 / 80 : ℝ) - (1309 / 3200 : ℝ)) ≤
      (1723124119912099 / 250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1309_denomUpper
    linarith [hpThetaJensenCell1309_product_upper]
  have hi : (1 / (1723124119912099 / 250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (131 / 80 : ℝ) - (1309 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1723124119912099 / 250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1723124119912099 / 250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1309 / 3200 : ℝ) - Real.pi * Real.exp (131 / 80 : ℝ)) := by
    rw [show (1309 / 3200 : ℝ) - Real.pi * Real.exp (131 / 80 : ℝ) =
      -(Real.pi * Real.exp (131 / 80 : ℝ) - (1309 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1309 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1309 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1309_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1723124119912099 / 250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1309_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1309 / 1600 : ℝ) (131 / 160 : ℝ) ≤ (1406117 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (131 / 80 : ℝ)) (3231001282222441 / 200000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (131 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1309_product_upper
  have hD : (67526469876339823 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1309 / 800 : ℝ) - (131 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell1309_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1309_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1309 / 800 : ℝ) - (131 / 320 : ℝ)) ≤
      (1 / (67526469876339823 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (67526469876339823 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((131 / 320 : ℝ) - Real.pi * Real.exp (1309 / 800 : ℝ)) ≤
      (2 / (67526469876339823 / 10000000000 : ℝ) : ℝ) := by
    rw [show (131 / 320 : ℝ) - Real.pi * Real.exp (1309 / 800 : ℝ) =
      -(Real.pi * Real.exp (1309 / 800 : ℝ) - (131 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (3231001282222441 / 200000000000000 : ℝ) ^ 2 - 6 *
      (3231001282222441 / 200000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1309_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1309 / 1600 : ℝ) (131 / 160 : ℝ)) :
    (2740721 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1406117 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1309_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1309_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1310_leftExp :
    (3213936053 / 625000000 : ℝ) ≤ Real.exp (131 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (131 / 80 : ℝ) (131562972103 / 125000000000 : ℝ)
    (3213936053 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1310_rightExp :
    Real.exp (1311 / 800 : ℝ) ≤ (51487295763 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1311 / 800 : ℝ) (1052544891057 / 1000000000000 : ℝ)
    (51487295763 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1310_denomUpper :
    Real.exp (157658377957970459 / 10000000000000000 : ℝ) ≤ (703098800948327 / 100000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (157658377957970459 / 10000000000000000 : ℝ)
    (102293792103 / 62500000000 : ℝ) (703098800948327 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1310_denomLower :
    (68881545896348663 / 10000000000 : ℝ) ≤ Real.exp (1230102638139547 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1230102638139547 / 78125000000000 : ℝ) (1635651269907 /
    1000000000000 : ℝ) (68881545896348663 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1310_product_lower :
    (1262109474077047 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (131 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1310_leftExp
    (by norm_num : (0 : ℝ) ≤ (3213936053 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1310_product_upper :
    Real.pi * Real.exp (1311 / 800 : ℝ) ≤ (161752127957970459 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1310_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1310_endpointLower :
    (2693807 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (131 / 160 : ℝ) (1311 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1262109474077047 / 78125000000000 : ℝ) (Real.pi * Real.exp (131 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell1310_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1311 / 800 : ℝ) - (131 / 320 : ℝ)) ≤
      (703098800948327 / 100000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1310_denomUpper
    linarith [hpThetaJensenCell1310_product_upper]
  have hi : (1 / (703098800948327 / 100000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1311 / 800 : ℝ) - (131 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (703098800948327 / 100000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (703098800948327 / 100000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((131 / 320 : ℝ) - Real.pi * Real.exp (1311 / 800 : ℝ)) := by
    rw [show (131 / 320 : ℝ) - Real.pi * Real.exp (1311 / 800 : ℝ) =
      -(Real.pi * Real.exp (1311 / 800 : ℝ) - (131 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (131 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (131 / 80 : ℝ)) := by
    have h := hpThetaJensenCell1310_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (703098800948327 / 100000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1310_endpointUpper :
    hpThetaJensenKernelEndpointUpper (131 / 160 : ℝ) (1311 / 1600 : ℝ) ≤ (691041 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1311 / 800 : ℝ)) (161752127957970459 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1311 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1310_product_upper
  have hD : (68881545896348663 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (131 / 80 : ℝ) - (1311 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1310_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1310_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (131 / 80 : ℝ) - (1311 / 3200 : ℝ)) ≤
      (1 / (68881545896348663 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (68881545896348663 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1311 / 3200 : ℝ) - Real.pi * Real.exp (131 / 80 : ℝ)) ≤
      (2 / (68881545896348663 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1311 / 3200 : ℝ) - Real.pi * Real.exp (131 / 80 : ℝ) =
      -(Real.pi * Real.exp (131 / 80 : ℝ) - (1311 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (161752127957970459 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (161752127957970459 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1310_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (131 / 160 : ℝ) (1311 / 1600 : ℝ)) :
    (2693807 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (691041 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1310_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1310_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1311_leftExp :
    (643591197 / 125000000 : ℝ) ≤ Real.exp (1311 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1311 / 800 : ℝ) (65784055691 / 62500000000 : ℝ)
    (643591197 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1311_rightExp :
    Real.exp (41 / 25 : ℝ) ≤ (12887923781 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (41 / 25 : ℝ) (210517201379 / 200000000000 : ℝ)
    (12887923781 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1311_denomUpper :
    Real.exp (39464392384923133 / 2500000000000000 : ℝ) ≤ (71724435321966743 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (39464392384923133 / 2500000000000000 : ℝ) (409429948479
    / 250000000000 : ℝ) (71724435321966743 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1311_denomLower :
    (3513279415074601 / 500000000 : ℝ) ≤ Real.exp (246331369470703 / 15625000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (246331369470703 / 15625000000000 : ℝ) (409167110941 /
    250000000000 : ℝ) (3513279415074601 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1311_product_lower :
    (252737619470703 / 15625000000000 : ℝ) ≤ Real.pi * Real.exp (1311 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1311_leftExp
    (by norm_num : (0 : ℝ) ≤ (643591197 / 125000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1311_product_upper :
    Real.pi * Real.exp (41 / 25 : ℝ) ≤ (40488611134923133 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1311_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1311_endpointLower :
    (661907 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (1311 / 1600 : ℝ) (41 / 50 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (252737619470703 / 15625000000000 : ℝ) (Real.pi * Real.exp (1311 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1311_product_lower
  have hD : Real.exp (Real.pi * Real.exp (41 / 25 : ℝ) - (1311 / 3200 : ℝ)) ≤
      (71724435321966743 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1311_denomUpper
    linarith [hpThetaJensenCell1311_product_upper]
  have hi : (1 / (71724435321966743 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (41 / 25 : ℝ) - (1311 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (71724435321966743 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (71724435321966743 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1311 / 3200 : ℝ) - Real.pi * Real.exp (41 / 25 : ℝ)) := by
    rw [show (1311 / 3200 : ℝ) - Real.pi * Real.exp (41 / 25 : ℝ) =
      -(Real.pi * Real.exp (41 / 25 : ℝ) - (1311 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1311 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1311 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1311_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (71724435321966743 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1311_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1311 / 1600 : ℝ) (41 / 50 : ℝ) ≤ (2716847 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (41 / 25 : ℝ)) (40488611134923133 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (41 / 50 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1311_product_upper
  have hD : (3513279415074601 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1311 / 800 : ℝ) - (41 / 100 : ℝ)) := by
    apply le_trans hpThetaJensenCell1311_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1311_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1311 / 800 : ℝ) - (41 / 100 : ℝ)) ≤
      (1 / (3513279415074601 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3513279415074601 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((41 / 100 : ℝ) - Real.pi * Real.exp (1311 / 800 : ℝ)) ≤
      (2 / (3513279415074601 / 500000000 : ℝ) : ℝ) := by
    rw [show (41 / 100 : ℝ) - Real.pi * Real.exp (1311 / 800 : ℝ) =
      -(Real.pi * Real.exp (1311 / 800 : ℝ) - (41 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (40488611134923133 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (40488611134923133 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1311_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1311 / 1600 : ℝ) (41 / 50 : ℝ)) :
    (661907 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2716847 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1311_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1311_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1312_leftExp :
    (51551695121 / 10000000000 : ℝ) ≤ Real.exp (41 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (41 / 25 : ℝ) (526293003447 / 500000000000 : ℝ)
    (51551695121 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1312_rightExp :
    Real.exp (1313 / 800 : ℝ) ≤ (25808087517 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1313 / 800 : ℝ) (1052627124339 / 1000000000000 : ℝ)
    (25808087517 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1312_denomUpper :
    Real.exp (79028507086794581 / 5000000000000000 : ℝ) ≤ (73169301339551263 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (79028507086794581 / 5000000000000000 : ℝ) (409685211163
    / 250000000000 : ℝ) (73169301339551263 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1312_denomLower :
    (17919812991591951 / 2500000000 : ℝ) ≤ Real.exp (19731408497321579 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (19731408497321579 / 1250000000000000 : ℝ) (818843771817
    / 500000000000 : ℝ) (17919812991591951 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1312_product_lower :
    (20244299122321579 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (41 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1312_leftExp
    (by norm_num : (0 : ℝ) ≤ (51551695121 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1312_product_upper :
    Real.pi * Real.exp (1313 / 800 : ℝ) ≤ (81078507086794581 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1312_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1312_endpointLower :
    (1301087 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (41 / 50 : ℝ) (1313 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (20244299122321579 / 1250000000000000 : ℝ) (Real.pi * Real.exp (41 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell1312_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1313 / 800 : ℝ) - (41 / 100 : ℝ)) ≤
      (73169301339551263 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1312_denomUpper
    linarith [hpThetaJensenCell1312_product_upper]
  have hi : (1 / (73169301339551263 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1313 / 800 : ℝ) - (41 / 100 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (73169301339551263 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (73169301339551263 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((41 / 100 : ℝ) - Real.pi * Real.exp (1313 / 800 : ℝ)) := by
    rw [show (41 / 100 : ℝ) - Real.pi * Real.exp (1313 / 800 : ℝ) =
      -(Real.pi * Real.exp (1313 / 800 : ℝ) - (41 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (41 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (41 / 25 : ℝ)) := by
    have h := hpThetaJensenCell1312_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (73169301339551263 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1312_endpointUpper :
    hpThetaJensenKernelEndpointUpper (41 / 50 : ℝ) (1313 / 1600 : ℝ) ≤ (41723 / 156250000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1313 / 800 : ℝ)) (81078507086794581 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1313 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1312_product_upper
  have hD : (17919812991591951 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (41 / 25 : ℝ) - (1313 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1312_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1312_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (41 / 25 : ℝ) - (1313 / 3200 : ℝ)) ≤
      (1 / (17919812991591951 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (17919812991591951 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1313 / 3200 : ℝ) - Real.pi * Real.exp (41 / 25 : ℝ)) ≤
      (2 / (17919812991591951 / 2500000000 : ℝ) : ℝ) := by
    rw [show (1313 / 3200 : ℝ) - Real.pi * Real.exp (41 / 25 : ℝ) =
      -(Real.pi * Real.exp (41 / 25 : ℝ) - (1313 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (81078507086794581 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (81078507086794581 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1312_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (41 / 50 : ℝ) (1313 / 1600 : ℝ)) :
    (1301087 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (41723 / 156250000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1312_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1312_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1313_leftExp :
    (6452021879 / 1250000000 : ℝ) ≤ Real.exp (1313 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1313 / 800 : ℝ) (526313562169 / 500000000000 : ℝ)
    (6452021879 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1313_rightExp :
    Real.exp (657 / 400 : ℝ) ≤ (10336147119 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (657 / 400 : ℝ) (1052668243389 / 1000000000000 : ℝ)
    (10336147119 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1313_denomUpper :
    Real.exp (31651342436020567 / 2000000000000000 : ℝ) ≤ (74645165006464927 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (31651342436020567 / 2000000000000000 : ℝ) (1639763830319
    / 1000000000000 : ℝ) (74645165006464927 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1313_denomLower :
    (36561603665404201 / 5000000000 : ℝ) ≤ Real.exp (2469542383611421 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2469542383611421 / 156250000000000 : ℝ) (1638708573949 /
    1000000000000 : ℝ) (36561603665404201 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1313_product_lower :
    (2533702539861421 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (1313 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1313_leftExp
    (by norm_num : (0 : ℝ) ≤ (6452021879 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1313_product_upper :
    Real.pi * Real.exp (657 / 400 : ℝ) ≤ (32471967436020567 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1313_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1313_endpointLower :
    (511487 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1313 / 1600 : ℝ) (657 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2533702539861421 / 156250000000000 : ℝ) (Real.pi * Real.exp (1313 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1313_product_lower
  have hD : Real.exp (Real.pi * Real.exp (657 / 400 : ℝ) - (1313 / 3200 : ℝ)) ≤
      (74645165006464927 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1313_denomUpper
    linarith [hpThetaJensenCell1313_product_upper]
  have hi : (1 / (74645165006464927 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (657 / 400 : ℝ) - (1313 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (74645165006464927 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (74645165006464927 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1313 / 3200 : ℝ) - Real.pi * Real.exp (657 / 400 : ℝ)) := by
    rw [show (1313 / 3200 : ℝ) - Real.pi * Real.exp (657 / 400 : ℝ) =
      -(Real.pi * Real.exp (657 / 400 : ℝ) - (1313 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1313 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1313 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1313_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (74645165006464927 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1313_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1313 / 1600 : ℝ) (657 / 800 : ℝ) ≤ (2624429 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (657 / 400 : ℝ)) (32471967436020567 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (657 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1313_product_upper
  have hD : (36561603665404201 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1313 / 800 : ℝ) - (657 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1313_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1313_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1313 / 800 : ℝ) - (657 / 1600 : ℝ)) ≤
      (1 / (36561603665404201 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (36561603665404201 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((657 / 1600 : ℝ) - Real.pi * Real.exp (1313 / 800 : ℝ)) ≤
      (2 / (36561603665404201 / 5000000000 : ℝ) : ℝ) := by
    rw [show (657 / 1600 : ℝ) - Real.pi * Real.exp (1313 / 800 : ℝ) =
      -(Real.pi * Real.exp (1313 / 800 : ℝ) - (657 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (32471967436020567 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (32471967436020567 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1313_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1313 / 1600 : ℝ) (657 / 800 : ℝ)) :
    (511487 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2624429 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1313_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1313_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1314_leftExp :
    (6460091949 / 1250000000 : ℝ) ≤ Real.exp (657 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (657 / 400 : ℝ) (263167060847 / 250000000000 : ℝ)
    (6460091949 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1314_rightExp :
    Real.exp (263 / 160 : ℝ) ≤ (25872688453 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (263 / 160 : ℝ) (210541872809 / 200000000000 : ℝ)
    (25872688453 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1314_denomUpper :
    Real.exp (79228331935125629 / 5000000000000000 : ℝ) ≤ (76152729472563931 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (79228331935125629 / 5000000000000000 : ℝ) (1640788755339
    / 1000000000000 : ℝ) (76152729472563931 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1314_denomLower :
    (18649535187987011 / 2500000000 : ℝ) ≤ Real.exp (2472662663905351 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2472662663905351 / 156250000000000 : ℝ) (409932884781 /
    250000000000 : ℝ) (18649535187987011 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1314_product_lower :
    (2536871648280351 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (657 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1314_leftExp
    (by norm_num : (0 : ℝ) ≤ (6460091949 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1314_product_upper :
    Real.pi * Real.exp (263 / 160 : ℝ) ≤ (81281456935125629 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1314_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1314_endpointLower :
    (1256701 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (657 / 800 : ℝ) (263 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2536871648280351 / 156250000000000 : ℝ) (Real.pi * Real.exp (657 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1314_product_lower
  have hD : Real.exp (Real.pi * Real.exp (263 / 160 : ℝ) - (657 / 1600 : ℝ)) ≤
      (76152729472563931 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1314_denomUpper
    linarith [hpThetaJensenCell1314_product_upper]
  have hi : (1 / (76152729472563931 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (263 / 160 : ℝ) - (657 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (76152729472563931 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (76152729472563931 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((657 / 1600 : ℝ) - Real.pi * Real.exp (263 / 160 : ℝ)) := by
    rw [show (657 / 1600 : ℝ) - Real.pi * Real.exp (263 / 160 : ℝ) =
      -(Real.pi * Real.exp (263 / 160 : ℝ) - (657 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (657 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (657 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1314_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (76152729472563931 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1314_endpointUpper :
    hpThetaJensenKernelEndpointUpper (657 / 800 : ℝ) (263 / 320 : ℝ) ≤ (2579307 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (263 / 160 : ℝ)) (81281456935125629 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (263 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1314_product_upper
  have hD : (18649535187987011 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (657 / 400 : ℝ) - (263 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1314_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1314_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (657 / 400 : ℝ) - (263 / 640 : ℝ)) ≤
      (1 / (18649535187987011 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (18649535187987011 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((263 / 640 : ℝ) - Real.pi * Real.exp (657 / 400 : ℝ)) ≤
      (2 / (18649535187987011 / 2500000000 : ℝ) : ℝ) := by
    rw [show (263 / 640 : ℝ) - Real.pi * Real.exp (657 / 400 : ℝ) =
      -(Real.pi * Real.exp (657 / 400 : ℝ) - (263 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (81281456935125629 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (81281456935125629 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1314_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (657 / 800 : ℝ) (263 / 320 : ℝ)) :
    (1256701 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2579307 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1314_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1314_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1315_leftExp :
    (6468172113 / 1250000000 : ℝ) ≤ Real.exp (263 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (263 / 160 : ℝ) (263177341011 / 250000000000 : ℝ)
    (6468172113 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1315_rightExp :
    Real.exp (329 / 200 : ℝ) ≤ (51810099071 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (329 / 200 : ℝ) (263187621577 / 250000000000 : ℝ)
    (51810099071 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1315_denomUpper :
    Real.exp (158656869570760103 / 10000000000000000 : ℝ) ≤ (7769271478082153 / 1000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (158656869570760103 / 10000000000000000 : ℝ)
    (820907812113 / 500000000000 : ℝ) (7769271478082153 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1315_denomLower :
    (15220951005690719 / 2000000000 : ℝ) ≤ Real.exp (2475786908102987 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2475786908102987 / 156250000000000 : ℝ) (328151288729 /
    200000000000 : ℝ) (15220951005690719 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1315_product_lower :
    (2540044720602987 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (263 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1315_leftExp
    (by norm_num : (0 : ℝ) ≤ (6468172113 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1315_product_upper :
    Real.pi * Real.exp (329 / 200 : ℝ) ≤ (162766244570760103 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1315_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1315_endpointLower :
    (2470063 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (263 / 320 : ℝ) (329 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2540044720602987 / 156250000000000 : ℝ) (Real.pi * Real.exp (263 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1315_product_lower
  have hD : Real.exp (Real.pi * Real.exp (329 / 200 : ℝ) - (263 / 640 : ℝ)) ≤
      (7769271478082153 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1315_denomUpper
    linarith [hpThetaJensenCell1315_product_upper]
  have hi : (1 / (7769271478082153 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (329 / 200 : ℝ) - (263 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7769271478082153 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7769271478082153 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((263 / 640 : ℝ) - Real.pi * Real.exp (329 / 200 : ℝ)) := by
    rw [show (263 / 640 : ℝ) - Real.pi * Real.exp (329 / 200 : ℝ) =
      -(Real.pi * Real.exp (329 / 200 : ℝ) - (263 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (263 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (263 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1315_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7769271478082153 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1315_endpointUpper :
    hpThetaJensenKernelEndpointUpper (263 / 320 : ℝ) (329 / 400 : ℝ) ≤ (158431 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (329 / 200 : ℝ)) (162766244570760103 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (329 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1315_product_upper
  have hD : (15220951005690719 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (263 / 160 : ℝ) - (329 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1315_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1315_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (263 / 160 : ℝ) - (329 / 800 : ℝ)) ≤
      (1 / (15220951005690719 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (15220951005690719 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((329 / 800 : ℝ) - Real.pi * Real.exp (263 / 160 : ℝ)) ≤
      (2 / (15220951005690719 / 2000000000 : ℝ) : ℝ) := by
    rw [show (329 / 800 : ℝ) - Real.pi * Real.exp (263 / 160 : ℝ) =
      -(Real.pi * Real.exp (263 / 160 : ℝ) - (329 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (162766244570760103 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (162766244570760103 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1315_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (263 / 320 : ℝ) (329 / 400 : ℝ)) :
    (2470063 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (158431 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1315_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1315_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1316_leftExp :
    (12952524767 / 2500000000 : ℝ) ≤ Real.exp (329 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (329 / 200 : ℝ) (1052750486307 / 1000000000000 : ℝ)
    (12952524767 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1316_rightExp :
    Real.exp (1317 / 800 : ℝ) ≤ (12968725547 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1317 / 800 : ℝ) (1052791610177 / 1000000000000 : ℝ)
    (12968725547 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1316_denomUpper :
    Real.exp (39714332397376371 / 2500000000000000 : ℝ) ≤ (79265858024677291 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (39714332397376371 / 2500000000000000 : ℝ) (1642844441409
    / 1000000000000 : ℝ) (79265858024677291 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1316_denomLower :
    (38821884828295993 / 5000000000 : ℝ) ≤ Real.exp (4957830242226133 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4957830242226133 / 312500000000000 : ℝ) (1641783291963 /
    1000000000000 : ℝ) (38821884828295993 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1316_product_lower :
    (5086443523476133 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (329 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1316_leftExp
    (by norm_num : (0 : ℝ) ≤ (12952524767 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1316_product_upper :
    Real.pi * Real.exp (1317 / 800 : ℝ) ≤ (40742457397376371 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1316_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1316_endpointLower :
    (2427409 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (329 / 400 : ℝ) (1317 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5086443523476133 / 312500000000000 : ℝ) (Real.pi * Real.exp (329 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1316_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1317 / 800 : ℝ) - (329 / 800 : ℝ)) ≤
      (79265858024677291 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1316_denomUpper
    linarith [hpThetaJensenCell1316_product_upper]
  have hi : (1 / (79265858024677291 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1317 / 800 : ℝ) - (329 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (79265858024677291 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (79265858024677291 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((329 / 800 : ℝ) - Real.pi * Real.exp (1317 / 800 : ℝ)) := by
    rw [show (329 / 800 : ℝ) - Real.pi * Real.exp (1317 / 800 : ℝ) =
      -(Real.pi * Real.exp (1317 / 800 : ℝ) - (329 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (329 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (329 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1316_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (79265858024677291 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1316_endpointUpper :
    hpThetaJensenKernelEndpointUpper (329 / 400 : ℝ) (1317 / 1600 : ℝ) ≤ (1245593 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1317 / 800 : ℝ)) (40742457397376371 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1317 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1316_product_upper
  have hD : (38821884828295993 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (329 / 200 : ℝ) - (1317 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1316_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1316_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (329 / 200 : ℝ) - (1317 / 3200 : ℝ)) ≤
      (1 / (38821884828295993 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (38821884828295993 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1317 / 3200 : ℝ) - Real.pi * Real.exp (329 / 200 : ℝ)) ≤
      (2 / (38821884828295993 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1317 / 3200 : ℝ) - Real.pi * Real.exp (329 / 200 : ℝ) =
      -(Real.pi * Real.exp (329 / 200 : ℝ) - (1317 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (40742457397376371 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (40742457397376371 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1316_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (329 / 400 : ℝ) (1317 / 1600 : ℝ)) :
    (2427409 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1245593 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1316_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1316_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1317_leftExp :
    (10374980437 / 2000000000 : ℝ) ≤ Real.exp (1317 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1317 / 800 : ℝ) (16449868909 / 15625000000 : ℝ)
    (10374980437 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1317_rightExp :
    Real.exp (659 / 400 : ℝ) ≤ (51939786361 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (659 / 400 : ℝ) (1052832735653 / 1000000000000 : ℝ)
    (51939786361 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1317_denomUpper :
    Real.exp (159058044253213073 / 10000000000000000 : ℝ) ≤ (80872914061028311 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (159058044253213073 / 10000000000000000 : ℝ)
    (1643875211421 / 1000000000000 : ℝ) (80872914061028311 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1317_denomLower :
    (19803980332906919 / 2500000000 : ℝ) ≤ Real.exp (3971275692629463 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3971275692629463 / 250000000000000 : ℝ) (205351511069 /
    125000000000 : ℝ) (19803980332906919 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1317_product_lower :
    (4074244442629463 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1317 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1317_leftExp
    (by norm_num : (0 : ℝ) ≤ (10374980437 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1317_product_upper :
    Real.pi * Real.exp (659 / 400 : ℝ) ≤ (163173669253213073 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1317_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1317_endpointLower :
    (2385431 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1317 / 1600 : ℝ) (659 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4074244442629463 / 250000000000000 : ℝ) (Real.pi * Real.exp (1317 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1317_product_lower
  have hD : Real.exp (Real.pi * Real.exp (659 / 400 : ℝ) - (1317 / 3200 : ℝ)) ≤
      (80872914061028311 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1317_denomUpper
    linarith [hpThetaJensenCell1317_product_upper]
  have hi : (1 / (80872914061028311 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (659 / 400 : ℝ) - (1317 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (80872914061028311 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (80872914061028311 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1317 / 3200 : ℝ) - Real.pi * Real.exp (659 / 400 : ℝ)) := by
    rw [show (1317 / 3200 : ℝ) - Real.pi * Real.exp (659 / 400 : ℝ) =
      -(Real.pi * Real.exp (659 / 400 : ℝ) - (1317 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1317 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1317 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1317_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (80872914061028311 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1317_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1317 / 1600 : ℝ) (659 / 800 : ℝ) ≤ (1224083 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (659 / 400 : ℝ)) (163173669253213073 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (659 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1317_product_upper
  have hD : (19803980332906919 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1317 / 800 : ℝ) - (659 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1317_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1317_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1317 / 800 : ℝ) - (659 / 1600 : ℝ)) ≤
      (1 / (19803980332906919 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (19803980332906919 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((659 / 1600 : ℝ) - Real.pi * Real.exp (1317 / 800 : ℝ)) ≤
      (2 / (19803980332906919 / 2500000000 : ℝ) : ℝ) := by
    rw [show (659 / 1600 : ℝ) - Real.pi * Real.exp (1317 / 800 : ℝ) =
      -(Real.pi * Real.exp (1317 / 800 : ℝ) - (659 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (163173669253213073 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (163173669253213073 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1317_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1317 / 1600 : ℝ) (659 / 800 : ℝ)) :
    (2385431 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1224083 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1317_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1317_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1318_leftExp :
    (25969893179 / 5000000000 : ℝ) ≤ Real.exp (659 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (659 / 400 : ℝ) (263208183913 / 250000000000 : ℝ)
    (25969893179 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1318_rightExp :
    Real.exp (1319 / 800 : ℝ) ≤ (6500593961 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1319 / 800 : ℝ) (210574772547 / 200000000000 : ℝ)
    (6500593961 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1318_denomUpper :
    Real.exp (19907376733719873 / 1250000000000000 : ℝ) ≤ (82514655666648529 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (19907376733719873 / 1250000000000000 : ℝ) (1644907938713
    / 1000000000000 : ℝ) (82514655666648529 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1318_denomLower :
    (80821964415171301 / 10000000000 : ℝ) ≤ Real.exp (9940733894000121 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (9940733894000121 / 625000000000000 : ℝ) (410960709483 /
    250000000000 : ℝ) (80821964415171301 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1318_product_lower :
    (10198351081500121 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (659 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1318_leftExp
    (by norm_num : (0 : ℝ) ≤ (25969893179 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1318_product_upper :
    Real.pi * Real.exp (1319 / 800 : ℝ) ≤ (20422220483719873 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1318_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1318_endpointLower :
    (2344119 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (659 / 800 : ℝ) (1319 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10198351081500121 / 625000000000000 : ℝ) (Real.pi * Real.exp (659 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1318_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1319 / 800 : ℝ) - (659 / 1600 : ℝ)) ≤
      (82514655666648529 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1318_denomUpper
    linarith [hpThetaJensenCell1318_product_upper]
  have hi : (1 / (82514655666648529 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1319 / 800 : ℝ) - (659 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (82514655666648529 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (82514655666648529 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((659 / 1600 : ℝ) - Real.pi * Real.exp (1319 / 800 : ℝ)) := by
    rw [show (659 / 1600 : ℝ) - Real.pi * Real.exp (1319 / 800 : ℝ) =
      -(Real.pi * Real.exp (1319 / 800 : ℝ) - (659 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (659 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (659 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1318_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (82514655666648529 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1318_endpointUpper :
    hpThetaJensenKernelEndpointUpper (659 / 800 : ℝ) (1319 / 1600 : ℝ) ≤ (2405829 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1319 / 800 : ℝ)) (20422220483719873 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1319 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1318_product_upper
  have hD : (80821964415171301 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (659 / 400 : ℝ) - (1319 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1318_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1318_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (659 / 400 : ℝ) - (1319 / 3200 : ℝ)) ≤
      (1 / (80821964415171301 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (80821964415171301 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1319 / 3200 : ℝ) - Real.pi * Real.exp (659 / 400 : ℝ)) ≤
      (2 / (80821964415171301 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1319 / 3200 : ℝ) - Real.pi * Real.exp (659 / 400 : ℝ) =
      -(Real.pi * Real.exp (659 / 400 : ℝ) - (1319 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (20422220483719873 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (20422220483719873 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1318_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (659 / 800 : ℝ) (1319 / 1600 : ℝ)) :
    (2344119 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2405829 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1318_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1318_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1319_leftExp :
    (26002375843 / 5000000000 : ℝ) ≤ Real.exp (1319 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1319 / 800 : ℝ) (526436931367 / 500000000000 : ℝ)
    (26002375843 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1319_rightExp :
    Real.exp (33 / 20 : ℝ) ≤ (52069798273 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (33 / 20 : ℝ) (1052914991423 / 1000000000000 : ℝ)
    (52069798273 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1319_denomUpper :
    Real.exp (159460238765868889 / 10000000000000000 : ℝ) ≤ (84191874282275031 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (159460238765868889 / 10000000000000000 : ℝ)
    (1645942627841 / 1000000000000 : ℝ) (84191874282275031 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1319_denomLower :
    (20615667804792013 / 2500000000 : ℝ) ≤ Real.exp (9953294491170257 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9953294491170257 / 625000000000000 : ℝ) (205609443071 /
    125000000000 : ℝ) (20615667804792013 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1319_product_lower :
    (10211106991170257 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1319 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1319_leftExp
    (by norm_num : (0 : ℝ) ≤ (26002375843 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1319_product_upper :
    Real.pi * Real.exp (33 / 20 : ℝ) ≤ (163582113765868889 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1319_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1319_endpointLower :
    (2303463 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1319 / 1600 : ℝ) (33 / 40 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10211106991170257 / 625000000000000 : ℝ) (Real.pi * Real.exp (1319 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1319_product_lower
  have hD : Real.exp (Real.pi * Real.exp (33 / 20 : ℝ) - (1319 / 3200 : ℝ)) ≤
      (84191874282275031 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1319_denomUpper
    linarith [hpThetaJensenCell1319_product_upper]
  have hi : (1 / (84191874282275031 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (33 / 20 : ℝ) - (1319 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (84191874282275031 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (84191874282275031 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1319 / 3200 : ℝ) - Real.pi * Real.exp (33 / 20 : ℝ)) := by
    rw [show (1319 / 3200 : ℝ) - Real.pi * Real.exp (33 / 20 : ℝ) =
      -(Real.pi * Real.exp (33 / 20 : ℝ) - (1319 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1319 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1319 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1319_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (84191874282275031 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1319_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1319 / 1600 : ℝ) (33 / 40 : ℝ) ≤ (1182081 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (33 / 20 : ℝ)) (163582113765868889 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (33 / 40 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1319_product_upper
  have hD : (20615667804792013 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1319 / 800 : ℝ) - (33 / 80 : ℝ)) := by
    apply le_trans hpThetaJensenCell1319_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1319_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1319 / 800 : ℝ) - (33 / 80 : ℝ)) ≤
      (1 / (20615667804792013 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (20615667804792013 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((33 / 80 : ℝ) - Real.pi * Real.exp (1319 / 800 : ℝ)) ≤
      (2 / (20615667804792013 / 2500000000 : ℝ) : ℝ) := by
    rw [show (33 / 80 : ℝ) - Real.pi * Real.exp (1319 / 800 : ℝ) =
      -(Real.pi * Real.exp (1319 / 800 : ℝ) - (33 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (163582113765868889 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (163582113765868889 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1319_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1319 / 1600 : ℝ) (33 / 40 : ℝ)) :
    (2303463 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1182081 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1319_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1319_endpointUpper

def hpThetaJensenCellsBatch065Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1598917 / 5000000000 : ℝ)
  | 1 => (314381 / 1000000000 : ℝ)
  | 2 => (3090621 / 10000000000 : ℝ)
  | 3 => (189891 / 625000000 : ℝ)
  | 4 => (1493351 / 5000000000 : ℝ)
  | 5 => (2935949 / 10000000000 : ℝ)
  | 6 => (577197 / 2000000000 : ℝ)
  | 7 => (1773 / 6250000 : ℝ)
  | 8 => (1394191 / 5000000000 : ℝ)
  | 9 => (2740721 / 10000000000 : ℝ)
  | 10 => (2693807 / 10000000000 : ℝ)
  | 11 => (661907 / 2500000000 : ℝ)
  | 12 => (1301087 / 5000000000 : ℝ)
  | 13 => (511487 / 2000000000 : ℝ)
  | 14 => (1256701 / 5000000000 : ℝ)
  | 15 => (2470063 / 10000000000 : ℝ)
  | 16 => (2427409 / 10000000000 : ℝ)
  | 17 => (2385431 / 10000000000 : ℝ)
  | 18 => (2344119 / 10000000000 : ℝ)
  | 19 => (2303463 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch065Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1640269 / 5000000000 : ℝ)
  | 1 => (3225197 / 10000000000 : ℝ)
  | 2 => (317071 / 1000000000 : ℝ)
  | 3 => (389633 / 1250000000 : ℝ)
  | 4 => (12257 / 40000000 : ℝ)
  | 5 => (1506127 / 5000000000 : ℝ)
  | 6 => (1480533 / 5000000000 : ℝ)
  | 7 => (2910673 / 10000000000 : ℝ)
  | 8 => (1430533 / 5000000000 : ℝ)
  | 9 => (1406117 / 5000000000 : ℝ)
  | 10 => (691041 / 2500000000 : ℝ)
  | 11 => (2716847 / 10000000000 : ℝ)
  | 12 => (41723 / 156250000 : ℝ)
  | 13 => (2624429 / 10000000000 : ℝ)
  | 14 => (2579307 / 10000000000 : ℝ)
  | 15 => (158431 / 625000000 : ℝ)
  | 16 => (1245593 / 5000000000 : ℝ)
  | 17 => (1224083 / 5000000000 : ℝ)
  | 18 => (2405829 / 10000000000 : ℝ)
  | 19 => (1182081 / 5000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch065_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1300 : ℝ) + (j.val : ℝ)) / 1600)
      (((1300 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch065Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch065Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1300_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1301_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1302_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1303_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1304_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1305_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1306_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1307_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1308_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1309_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1310_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1311_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1312_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1313_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1314_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1315_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1316_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1317_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1318_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1319_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper] at h ⊢
    exact h

end HodgeProofHP
