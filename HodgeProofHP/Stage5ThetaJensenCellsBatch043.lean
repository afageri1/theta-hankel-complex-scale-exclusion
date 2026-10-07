import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell860_leftExp :
    (7324982251 / 2500000000 : ℝ) ≤ Real.exp (43 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (43 / 40 : ℝ) (1034164392093 / 1000000000000 : ℝ)
    (7324982251 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell860_rightExp :
    Real.exp (861 / 800 : ℝ) ≤ (14668288409 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (861 / 800 : ℝ) (103420478993 / 100000000000 : ℝ)
    (14668288409 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell860_denomUpper :
    Real.exp (44738042187695537 / 5000000000000000 : ℝ) ≤ (76894799818131 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (44738042187695537 / 5000000000000000 : ℝ) (3306543869 /
    2500000000 : ℝ) (76894799818131 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell860_denomLower :
    (75990594036071 / 10000000000 : ℝ) ≤ Real.exp (2792431173735449 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2792431173735449 / 312500000000000 : ℝ) (264425747453 /
    200000000000 : ℝ) (75990594036071 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell860_product_lower :
    (2876513204985449 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (43 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell860_leftExp
    (by norm_num : (0 : ℝ) ≤ (7324982251 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell860_product_upper :
    Real.pi * Real.exp (861 / 800 : ℝ) ≤ (46081792187695537 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell860_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell860_endpointLower :
    (737858557 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (43 / 80 : ℝ) (861 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2876513204985449 / 312500000000000 : ℝ) (Real.pi * Real.exp (43 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell860_product_lower
  have hD : Real.exp (Real.pi * Real.exp (861 / 800 : ℝ) - (43 / 160 : ℝ)) ≤
      (76894799818131 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell860_denomUpper
    linarith [hpThetaJensenCell860_product_upper]
  have hi : (1 / (76894799818131 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (861 / 800 : ℝ) - (43 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (76894799818131 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (76894799818131 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((43 / 160 : ℝ) - Real.pi * Real.exp (861 / 800 : ℝ)) := by
    rw [show (43 / 160 : ℝ) - Real.pi * Real.exp (861 / 800 : ℝ) =
      -(Real.pi * Real.exp (861 / 800 : ℝ) - (43 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (43 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (43 / 40 : ℝ)) := by
    have h := hpThetaJensenCell860_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (76894799818131 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell860_endpointUpper :
    hpThetaJensenKernelEndpointUpper (43 / 80 : ℝ) (861 / 1600 : ℝ) ≤ (750661463 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (861 / 800 : ℝ)) (46081792187695537 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (861 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell860_product_upper
  have hD : (75990594036071 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (43 / 40 : ℝ) - (861 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell860_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell860_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (43 / 40 : ℝ) - (861 / 3200 : ℝ)) ≤
      (1 / (75990594036071 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (75990594036071 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((861 / 3200 : ℝ) - Real.pi * Real.exp (43 / 40 : ℝ)) ≤
      (2 / (75990594036071 / 10000000000 : ℝ) : ℝ) := by
    rw [show (861 / 3200 : ℝ) - Real.pi * Real.exp (43 / 40 : ℝ) =
      -(Real.pi * Real.exp (43 / 40 : ℝ) - (861 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (46081792187695537 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (46081792187695537 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell860_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (43 / 80 : ℝ) (861 / 1600 : ℝ)) :
    (737858557 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (750661463 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell860_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell860_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell861_leftExp :
    (1833536051 / 625000000 : ℝ) ≤ Real.exp (861 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (861 / 800 : ℝ) (1034204789929 / 1000000000000 : ℝ)
    (1833536051 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell861_rightExp :
    Real.exp (431 / 400 : ℝ) ≤ (29373270467 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (431 / 400 : ℝ) (1034245189343 / 1000000000000 : ℝ)
    (29373270467 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell861_denomUpper :
    Real.exp (89588235886233931 / 10000000000000000 : ℝ) ≤ (77762040643369 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (89588235886233931 / 10000000000000000 : ℝ) (661540585601
    / 500000000000 : ℝ) (77762040643369 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell861_denomLower :
    (9605816261387 / 1250000000 : ℝ) ≤ Real.exp (698982851816649 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (698982851816649 / 78125000000000 : ℝ) (6612957971 /
    5000000000 : ℝ) (9605816261387 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell861_product_lower :
    (720027773691649 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (861 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell861_leftExp
    (by norm_num : (0 : ℝ) ≤ (1833536051 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell861_product_upper :
    Real.pi * Real.exp (431 / 400 : ℝ) ≤ (92278860886233931 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell861_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell861_endpointLower :
    (9145423 / 125000000 : ℝ) ≤ hpThetaTraceEndpointLower (861 / 1600 : ℝ) (431 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (720027773691649 / 78125000000000 : ℝ) (Real.pi * Real.exp (861 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell861_product_lower
  have hD : Real.exp (Real.pi * Real.exp (431 / 400 : ℝ) - (861 / 3200 : ℝ)) ≤
      (77762040643369 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell861_denomUpper
    linarith [hpThetaJensenCell861_product_upper]
  have hi : (1 / (77762040643369 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (431 / 400 : ℝ) - (861 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (77762040643369 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (77762040643369 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((861 / 3200 : ℝ) - Real.pi * Real.exp (431 / 400 : ℝ)) := by
    rw [show (861 / 3200 : ℝ) - Real.pi * Real.exp (431 / 400 : ℝ) =
      -(Real.pi * Real.exp (431 / 400 : ℝ) - (861 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (861 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (861 / 800 : ℝ)) := by
    have h := hpThetaJensenCell861_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (77762040643369 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell861_endpointUpper :
    hpThetaJensenKernelEndpointUpper (861 / 1600 : ℝ) (431 / 800 : ℝ) ≤ (744339189 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (431 / 400 : ℝ)) (92278860886233931 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (431 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell861_product_upper
  have hD : (9605816261387 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (861 / 800 : ℝ) - (431 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell861_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell861_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (861 / 800 : ℝ) - (431 / 1600 : ℝ)) ≤
      (1 / (9605816261387 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (9605816261387 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((431 / 1600 : ℝ) - Real.pi * Real.exp (861 / 800 : ℝ)) ≤
      (2 / (9605816261387 / 1250000000 : ℝ) : ℝ) := by
    rw [show (431 / 1600 : ℝ) - Real.pi * Real.exp (861 / 800 : ℝ) =
      -(Real.pi * Real.exp (861 / 800 : ℝ) - (431 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (92278860886233931 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (92278860886233931 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell861_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (861 / 1600 : ℝ) (431 / 800 : ℝ)) :
    (9145423 / 125000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (744339189 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell861_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell861_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell862_leftExp :
    (5874654093 / 2000000000 : ℝ) ≤ Real.exp (431 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (431 / 400 : ℝ) (517122594671 / 500000000000 : ℝ)
    (5874654093 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell862_rightExp :
    Real.exp (863 / 800 : ℝ) ≤ (29410010013 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (863 / 800 : ℝ) (206857118067 / 200000000000 : ℝ)
    (29410010013 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell862_denomUpper :
    Real.exp (89700531586770709 / 10000000000000000 : ℝ) ≤ (78640196352577 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (89700531586770709 / 10000000000000000 : ℝ) (13235455537
    / 10000000000 : ℝ) (78640196352577 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell862_denomLower :
    (621705809859 / 80000000 : ℝ) ≤ Real.exp (2239548912667007 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2239548912667007 / 250000000000000 : ℝ) (1323055208553 /
    1000000000000 : ℝ) (621705809859 / 80000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell862_product_lower :
    (2306970787667007 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (431 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell862_leftExp
    (by norm_num : (0 : ℝ) ≤ (5874654093 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell862_product_upper :
    Real.pi * Real.exp (863 / 800 : ℝ) ≤ (92394281586770709 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell862_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell862_endpointLower :
    (22670341 / 312500000 : ℝ) ≤ hpThetaTraceEndpointLower (431 / 800 : ℝ) (863 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2306970787667007 / 250000000000000 : ℝ) (Real.pi * Real.exp (431 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell862_product_lower
  have hD : Real.exp (Real.pi * Real.exp (863 / 800 : ℝ) - (431 / 1600 : ℝ)) ≤
      (78640196352577 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell862_denomUpper
    linarith [hpThetaJensenCell862_product_upper]
  have hi : (1 / (78640196352577 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (863 / 800 : ℝ) - (431 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (78640196352577 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (78640196352577 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((431 / 1600 : ℝ) - Real.pi * Real.exp (863 / 800 : ℝ)) := by
    rw [show (431 / 1600 : ℝ) - Real.pi * Real.exp (863 / 800 : ℝ) =
      -(Real.pi * Real.exp (863 / 800 : ℝ) - (431 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (431 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (431 / 400 : ℝ)) := by
    have h := hpThetaJensenCell862_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (78640196352577 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell862_endpointUpper :
    hpThetaJensenKernelEndpointUpper (431 / 800 : ℝ) (863 / 1600 : ℝ) ≤ (184514817 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (863 / 800 : ℝ)) (92394281586770709 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (863 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell862_product_upper
  have hD : (621705809859 / 80000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (431 / 400 : ℝ) - (863 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell862_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell862_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (431 / 400 : ℝ) - (863 / 3200 : ℝ)) ≤
      (1 / (621705809859 / 80000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (621705809859 / 80000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((863 / 3200 : ℝ) - Real.pi * Real.exp (431 / 400 : ℝ)) ≤
      (2 / (621705809859 / 80000000 : ℝ) : ℝ) := by
    rw [show (863 / 3200 : ℝ) - Real.pi * Real.exp (431 / 400 : ℝ) =
      -(Real.pi * Real.exp (431 / 400 : ℝ) - (863 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (92394281586770709 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (92394281586770709 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell862_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (431 / 800 : ℝ) (863 / 1600 : ℝ)) :
    (22670341 / 312500000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (184514817 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell862_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell862_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell863_leftExp :
    (29410010011 / 10000000000 : ℝ) ≤ Real.exp (863 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (863 / 800 : ℝ) (517142795167 / 500000000000 : ℝ)
    (29410010011 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell863_rightExp :
    Real.exp (27 / 25 : ℝ) ≤ (3680849439 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (27 / 25 : ℝ) (206865198581 / 200000000000 : ℝ)
    (3680849439 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell863_denomUpper :
    Real.exp (11226621456616327 / 1250000000000000 : ℝ) ≤ (39764708537369 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11226621456616327 / 1250000000000000 : ℝ) (331002674127
    / 250000000000 : ℝ) (39764708537369 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell863_denomLower :
    (78590830399511 / 10000000000 : ℝ) ≤ Real.exp (11211781521309689 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11211781521309689 / 1250000000000000 : ℝ) (1323519581787
    / 1000000000000 : ℝ) (78590830399511 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell863_product_lower :
    (11549281521309689 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (863 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell863_leftExp
    (by norm_num : (0 : ℝ) ≤ (29410010011 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell863_product_upper :
    Real.pi * Real.exp (27 / 25 : ℝ) ≤ (11563730831616327 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell863_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell863_endpointLower :
    (71930959 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (863 / 1600 : ℝ) (27 / 50 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11549281521309689 / 1250000000000000 : ℝ) (Real.pi * Real.exp (863 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell863_product_lower
  have hD : Real.exp (Real.pi * Real.exp (27 / 25 : ℝ) - (863 / 3200 : ℝ)) ≤
      (39764708537369 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell863_denomUpper
    linarith [hpThetaJensenCell863_product_upper]
  have hi : (1 / (39764708537369 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (27 / 25 : ℝ) - (863 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (39764708537369 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (39764708537369 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((863 / 3200 : ℝ) - Real.pi * Real.exp (27 / 25 : ℝ)) := by
    rw [show (863 / 3200 : ℝ) - Real.pi * Real.exp (27 / 25 : ℝ) =
      -(Real.pi * Real.exp (27 / 25 : ℝ) - (863 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (863 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (863 / 800 : ℝ)) := by
    have h := hpThetaJensenCell863_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (39764708537369 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell863_endpointUpper :
    hpThetaJensenKernelEndpointUpper (863 / 1600 : ℝ) (27 / 50 : ℝ) ≤ (91477689 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (27 / 25 : ℝ)) (11563730831616327 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (27 / 50 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell863_product_upper
  have hD : (78590830399511 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (863 / 800 : ℝ) - (27 / 100 : ℝ)) := by
    apply le_trans hpThetaJensenCell863_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell863_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (863 / 800 : ℝ) - (27 / 100 : ℝ)) ≤
      (1 / (78590830399511 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (78590830399511 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((27 / 100 : ℝ) - Real.pi * Real.exp (863 / 800 : ℝ)) ≤
      (2 / (78590830399511 / 10000000000 : ℝ) : ℝ) := by
    rw [show (27 / 100 : ℝ) - Real.pi * Real.exp (863 / 800 : ℝ) =
      -(Real.pi * Real.exp (863 / 800 : ℝ) - (27 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (11563730831616327 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (11563730831616327 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell863_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (863 / 1600 : ℝ) (27 / 50 : ℝ)) :
    (71930959 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (91477689 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell863_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell863_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell864_leftExp :
    (2944679551 / 1000000000 : ℝ) ≤ Real.exp (27 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (27 / 25 : ℝ) (129290749113 / 125000000000 : ℝ)
    (2944679551 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell864_rightExp :
    Real.exp (173 / 160 : ℝ) ≤ (29483627021 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (173 / 160 : ℝ) (1034366397053 / 1000000000000 : ℝ)
    (29483627021 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell864_denomUpper :
    Real.exp (89925556263784453 / 10000000000000000 : ℝ) ≤ (1005373189813 / 125000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (89925556263784453 / 10000000000000000 : ℝ)
    (1324476601053 / 1000000000000 : ℝ) (1005373189813 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell864_denomLower :
    (79479492625261 / 10000000000 : ℝ) ≤ Real.exp (1122583652498149 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1122583652498149 / 125000000000000 : ℝ) (264796943063 /
    200000000000 : ℝ) (79479492625261 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell864_product_lower :
    (1156372714998149 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (27 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell864_leftExp
    (by norm_num : (0 : ℝ) ≤ (2944679551 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell864_product_upper :
    Real.pi * Real.exp (173 / 160 : ℝ) ≤ (92625556263784453 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell864_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell864_endpointLower :
    (71320969 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (27 / 50 : ℝ) (173 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1156372714998149 / 125000000000000 : ℝ) (Real.pi * Real.exp (27 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell864_product_lower
  have hD : Real.exp (Real.pi * Real.exp (173 / 160 : ℝ) - (27 / 100 : ℝ)) ≤
      (1005373189813 / 125000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell864_denomUpper
    linarith [hpThetaJensenCell864_product_upper]
  have hi : (1 / (1005373189813 / 125000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (173 / 160 : ℝ) - (27 / 100 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1005373189813 / 125000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1005373189813 / 125000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((27 / 100 : ℝ) - Real.pi * Real.exp (173 / 160 : ℝ)) := by
    rw [show (27 / 100 : ℝ) - Real.pi * Real.exp (173 / 160 : ℝ) =
      -(Real.pi * Real.exp (173 / 160 : ℝ) - (27 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (27 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (27 / 25 : ℝ)) := by
    have h := hpThetaJensenCell864_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1005373189813 / 125000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell864_endpointUpper :
    hpThetaJensenKernelEndpointUpper (27 / 50 : ℝ) (173 / 320 : ℝ) ≤ (725625739 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (173 / 160 : ℝ)) (92625556263784453 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (173 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell864_product_upper
  have hD : (79479492625261 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (27 / 25 : ℝ) - (173 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell864_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell864_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (27 / 25 : ℝ) - (173 / 640 : ℝ)) ≤
      (1 / (79479492625261 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (79479492625261 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((173 / 640 : ℝ) - Real.pi * Real.exp (27 / 25 : ℝ)) ≤
      (2 / (79479492625261 / 10000000000 : ℝ) : ℝ) := by
    rw [show (173 / 640 : ℝ) - Real.pi * Real.exp (27 / 25 : ℝ) =
      -(Real.pi * Real.exp (27 / 25 : ℝ) - (173 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (92625556263784453 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (92625556263784453 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell864_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (27 / 50 : ℝ) (173 / 320 : ℝ)) :
    (71320969 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (725625739 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell864_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell864_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell865_leftExp :
    (29483627019 / 10000000000 : ℝ) ≤ Real.exp (173 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (173 / 160 : ℝ) (258591599263 / 250000000000 : ℝ)
    (29483627019 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell865_rightExp :
    Real.exp (433 / 400 : ℝ) ≤ (29520504599 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (433 / 400 : ℝ) (51720340139 / 50000000000 : ℝ)
    (29520504599 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell865_denomUpper :
    Real.exp (90038285604686207 / 10000000000000000 : ℝ) ≤ (10167708171579 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (90038285604686207 / 10000000000000000 : ℝ)
    (1324943268791 / 1000000000000 : ℝ) (10167708171579 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell865_denomLower :
    (10047420648871 / 1250000000 : ℝ) ≤ Real.exp (11239909596734281 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11239909596734281 / 1250000000000000 : ℝ) (264890122113
    / 200000000000 : ℝ) (10047420648871 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell865_product_lower :
    (11578190846734281 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (173 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell865_leftExp
    (by norm_num : (0 : ℝ) ≤ (29483627019 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell865_product_upper :
    Real.pi * Real.exp (433 / 400 : ℝ) ≤ (92741410604686207 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell865_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell865_endpointLower :
    (70715103 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (173 / 320 : ℝ) (433 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11578190846734281 / 1250000000000000 : ℝ) (Real.pi * Real.exp (173 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell865_product_lower
  have hD : Real.exp (Real.pi * Real.exp (433 / 400 : ℝ) - (173 / 640 : ℝ)) ≤
      (10167708171579 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell865_denomUpper
    linarith [hpThetaJensenCell865_product_upper]
  have hi : (1 / (10167708171579 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (433 / 400 : ℝ) - (173 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (10167708171579 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (10167708171579 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((173 / 640 : ℝ) - Real.pi * Real.exp (433 / 400 : ℝ)) := by
    rw [show (173 / 640 : ℝ) - Real.pi * Real.exp (433 / 400 : ℝ) =
      -(Real.pi * Real.exp (433 / 400 : ℝ) - (173 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (173 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (173 / 160 : ℝ)) := by
    have h := hpThetaJensenCell865_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (10167708171579 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell865_endpointUpper :
    hpThetaJensenKernelEndpointUpper (173 / 320 : ℝ) (433 / 800 : ℝ) ≤ (719471761 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (433 / 400 : ℝ)) (92741410604686207 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (433 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell865_product_upper
  have hD : (10047420648871 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (173 / 160 : ℝ) - (433 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell865_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell865_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (173 / 160 : ℝ) - (433 / 1600 : ℝ)) ≤
      (1 / (10047420648871 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (10047420648871 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((433 / 1600 : ℝ) - Real.pi * Real.exp (173 / 160 : ℝ)) ≤
      (2 / (10047420648871 / 1250000000 : ℝ) : ℝ) := by
    rw [show (433 / 1600 : ℝ) - Real.pi * Real.exp (173 / 160 : ℝ) =
      -(Real.pi * Real.exp (173 / 160 : ℝ) - (433 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (92741410604686207 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (92741410604686207 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell865_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (173 / 320 : ℝ) (433 / 800 : ℝ)) :
    (70715103 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (719471761 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell865_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell865_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell866_leftExp :
    (29520504597 / 10000000000 : ℝ) ≤ Real.exp (433 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (433 / 400 : ℝ) (1034406802779 / 1000000000000 : ℝ)
    (29520504597 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell866_rightExp :
    Real.exp (867 / 800 : ℝ) ≤ (14778714151 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (867 / 800 : ℝ) (206889442017 / 200000000000 : ℝ)
    (14778714151 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell866_denomUpper :
    Real.exp (45075579925782543 / 5000000000000000 : ℝ) ≤ (82265004552211 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (45075579925782543 / 5000000000000000 : ℝ) (1325410701143
    / 1000000000000 : ℝ) (82265004552211 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell866_denomLower :
    (40645301344307 / 5000000000 : ℝ) ≤ Real.exp (11254000759737303 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11254000759737303 / 1250000000000000 : ℝ) (1324917268993
    / 1000000000000 : ℝ) (40645301344307 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell866_product_lower :
    (11592672634737303 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (433 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell866_leftExp
    (by norm_num : (0 : ℝ) ≤ (29520504597 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell866_product_upper :
    Real.pi * Real.exp (867 / 800 : ℝ) ≤ (46428704925782543 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell866_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell866_endpointLower :
    (43820839 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (433 / 800 : ℝ) (867 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11592672634737303 / 1250000000000000 : ℝ) (Real.pi * Real.exp (433 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell866_product_lower
  have hD : Real.exp (Real.pi * Real.exp (867 / 800 : ℝ) - (433 / 1600 : ℝ)) ≤
      (82265004552211 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell866_denomUpper
    linarith [hpThetaJensenCell866_product_upper]
  have hi : (1 / (82265004552211 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (867 / 800 : ℝ) - (433 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (82265004552211 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (82265004552211 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((433 / 1600 : ℝ) - Real.pi * Real.exp (867 / 800 : ℝ)) := by
    rw [show (433 / 1600 : ℝ) - Real.pi * Real.exp (867 / 800 : ℝ) =
      -(Real.pi * Real.exp (867 / 800 : ℝ) - (433 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (433 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (433 / 400 : ℝ)) := by
    have h := hpThetaJensenCell866_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (82265004552211 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell866_endpointUpper :
    hpThetaJensenKernelEndpointUpper (433 / 800 : ℝ) (867 / 1600 : ℝ) ≤ (713359393 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (867 / 800 : ℝ)) (46428704925782543 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (867 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell866_product_upper
  have hD : (40645301344307 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (433 / 400 : ℝ) - (867 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell866_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell866_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (433 / 400 : ℝ) - (867 / 3200 : ℝ)) ≤
      (1 / (40645301344307 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (40645301344307 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((867 / 3200 : ℝ) - Real.pi * Real.exp (433 / 400 : ℝ)) ≤
      (2 / (40645301344307 / 5000000000 : ℝ) : ℝ) := by
    rw [show (867 / 3200 : ℝ) - Real.pi * Real.exp (433 / 400 : ℝ) =
      -(Real.pi * Real.exp (433 / 400 : ℝ) - (867 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (46428704925782543 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (46428704925782543 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell866_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (433 / 800 : ℝ) (867 / 1600 : ℝ)) :
    (43820839 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (713359393 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell866_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell866_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell867_leftExp :
    (295574283 / 100000000 : ℝ) ≤ Real.exp (867 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (867 / 800 : ℝ) (258611802521 / 250000000000 : ℝ)
    (295574283 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell867_rightExp :
    Real.exp (217 / 200 : ℝ) ≤ (7398599547 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (217 / 200 : ℝ) (129310952371 / 125000000000 : ℝ)
    (7398599547 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell867_denomUpper :
    Real.exp (22566044796658371 / 2500000000000000 : ℝ) ≤ (41600016010457 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (22566044796658371 / 2500000000000000 : ℝ) (1325878899557
    / 1000000000000 : ℝ) (41600016010457 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell867_denomLower :
    (41106680967163 / 5000000000 : ℝ) ≤ Real.exp (112681100359817 / 12500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (112681100359817 / 12500000000000 : ℝ) (66269234601 /
    50000000000 : ℝ) (41106680967163 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell867_product_lower :
    (116071725359817 / 12500000000000 : ℝ) ≤ Real.pi * Real.exp (867 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell867_leftExp
    (by norm_num : (0 : ℝ) ≤ (295574283 / 100000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell867_product_upper :
    Real.pi * Real.exp (217 / 200 : ℝ) ≤ (23243388546658371 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell867_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell867_endpointLower :
    (695156691 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (867 / 1600 : ℝ) (217 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (116071725359817 / 12500000000000 : ℝ) (Real.pi * Real.exp (867 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell867_product_lower
  have hD : Real.exp (Real.pi * Real.exp (217 / 200 : ℝ) - (867 / 3200 : ℝ)) ≤
      (41600016010457 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell867_denomUpper
    linarith [hpThetaJensenCell867_product_upper]
  have hi : (1 / (41600016010457 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (217 / 200 : ℝ) - (867 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (41600016010457 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (41600016010457 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((867 / 3200 : ℝ) - Real.pi * Real.exp (217 / 200 : ℝ)) := by
    rw [show (867 / 3200 : ℝ) - Real.pi * Real.exp (217 / 200 : ℝ) =
      -(Real.pi * Real.exp (217 / 200 : ℝ) - (867 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (867 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (867 / 800 : ℝ)) := by
    have h := hpThetaJensenCell867_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (41600016010457 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell867_endpointUpper :
    hpThetaJensenKernelEndpointUpper (867 / 1600 : ℝ) (217 / 400 : ℝ) ≤ (707288451 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (217 / 200 : ℝ)) (23243388546658371 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (217 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell867_product_upper
  have hD : (41106680967163 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (867 / 800 : ℝ) - (217 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell867_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell867_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (867 / 800 : ℝ) - (217 / 800 : ℝ)) ≤
      (1 / (41106680967163 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (41106680967163 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((217 / 800 : ℝ) - Real.pi * Real.exp (867 / 800 : ℝ)) ≤
      (2 / (41106680967163 / 5000000000 : ℝ) : ℝ) := by
    rw [show (217 / 800 : ℝ) - Real.pi * Real.exp (867 / 800 : ℝ) =
      -(Real.pi * Real.exp (867 / 800 : ℝ) - (217 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (23243388546658371 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (23243388546658371 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell867_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (867 / 1600 : ℝ) (217 / 400 : ℝ)) :
    (695156691 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (707288451 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell867_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell867_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell868_leftExp :
    (14797199093 / 5000000000 : ℝ) ≤ Real.exp (217 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (217 / 200 : ℝ) (1034487618967 / 1000000000000 : ℝ)
    (14797199093 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell868_rightExp :
    Real.exp (869 / 800 : ℝ) ≤ (7407853579 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (869 / 800 : ℝ) (103452802943 / 100000000000 : ℝ)
    (7407853579 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell868_denomUpper :
    Real.exp (22594335948811347 / 2500000000000000 : ℝ) ≤ (1682938189433 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (22594335948811347 / 2500000000000000 : ℝ) (265269573099
    / 200000000000 : ℝ) (1682938189433 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell868_denomLower :
    (41573901060581 / 5000000000 : ℝ) ≤ Real.exp (5641118724122007 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5641118724122007 / 625000000000000 : ℝ) (331463220273 /
    250000000000 : ℝ) (41573901060581 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell868_product_lower :
    (5810845286622007 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (217 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell868_leftExp
    (by norm_num : (0 : ℝ) ≤ (14797199093 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell868_product_upper :
    Real.pi * Real.exp (869 / 800 : ℝ) ≤ (23272460948811347 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell868_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell868_endpointLower :
    (137844129 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (217 / 400 : ℝ) (869 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5810845286622007 / 625000000000000 : ℝ) (Real.pi * Real.exp (217 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell868_product_lower
  have hD : Real.exp (Real.pi * Real.exp (869 / 800 : ℝ) - (217 / 800 : ℝ)) ≤
      (1682938189433 / 200000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell868_denomUpper
    linarith [hpThetaJensenCell868_product_upper]
  have hi : (1 / (1682938189433 / 200000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (869 / 800 : ℝ) - (217 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1682938189433 / 200000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1682938189433 / 200000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((217 / 800 : ℝ) - Real.pi * Real.exp (869 / 800 : ℝ)) := by
    rw [show (217 / 800 : ℝ) - Real.pi * Real.exp (869 / 800 : ℝ) =
      -(Real.pi * Real.exp (869 / 800 : ℝ) - (217 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (217 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (217 / 200 : ℝ)) := by
    have h := hpThetaJensenCell868_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1682938189433 / 200000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell868_endpointUpper :
    hpThetaJensenKernelEndpointUpper (217 / 400 : ℝ) (869 / 1600 : ℝ) ≤ (701258749 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (869 / 800 : ℝ)) (23272460948811347 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (869 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell868_product_upper
  have hD : (41573901060581 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (217 / 200 : ℝ) - (869 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell868_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell868_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (217 / 200 : ℝ) - (869 / 3200 : ℝ)) ≤
      (1 / (41573901060581 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (41573901060581 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((869 / 3200 : ℝ) - Real.pi * Real.exp (217 / 200 : ℝ)) ≤
      (2 / (41573901060581 / 5000000000 : ℝ) : ℝ) := by
    rw [show (869 / 3200 : ℝ) - Real.pi * Real.exp (217 / 200 : ℝ) =
      -(Real.pi * Real.exp (217 / 200 : ℝ) - (869 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (23272460948811347 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (23272460948811347 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell868_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (217 / 400 : ℝ) (869 / 1600 : ℝ)) :
    (137844129 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (701258749 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell868_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell868_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell869_leftExp :
    (14815707157 / 5000000000 : ℝ) ≤ Real.exp (869 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (869 / 800 : ℝ) (1034528029429 / 1000000000000 : ℝ)
    (14815707157 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell869_rightExp :
    Real.exp (87 / 80 : ℝ) ≤ (29668476743 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (87 / 80 : ℝ) (103456844147 / 100000000000 : ℝ)
    (29668476743 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell869_denomUpper :
    Real.exp (90490653856471599 / 10000000000000000 : ℝ) ≤ (85105800962307 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (90490653856471599 / 10000000000000000 : ℝ)
    (1326817600399 / 1000000000000 : ℝ) (85105800962307 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell869_denomLower :
    (21023521212113 / 2500000000 : ℝ) ≤ Real.exp (5648191509846743 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5648191509846743 / 625000000000000 : ℝ) (53052873507 /
    40000000000 : ℝ) (21023521212113 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell869_product_lower :
    (5818113384846743 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (869 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell869_leftExp
    (by norm_num : (0 : ℝ) ≤ (14815707157 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell869_product_upper :
    Real.pi * Real.exp (87 / 80 : ℝ) ≤ (93206278856471599 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell869_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell869_endpointLower :
    (42707819 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (869 / 1600 : ℝ) (87 / 160 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5818113384846743 / 625000000000000 : ℝ) (Real.pi * Real.exp (869 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell869_product_lower
  have hD : Real.exp (Real.pi * Real.exp (87 / 80 : ℝ) - (869 / 3200 : ℝ)) ≤
      (85105800962307 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell869_denomUpper
    linarith [hpThetaJensenCell869_product_upper]
  have hi : (1 / (85105800962307 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (87 / 80 : ℝ) - (869 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (85105800962307 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (85105800962307 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((869 / 3200 : ℝ) - Real.pi * Real.exp (87 / 80 : ℝ)) := by
    rw [show (869 / 3200 : ℝ) - Real.pi * Real.exp (87 / 80 : ℝ) =
      -(Real.pi * Real.exp (87 / 80 : ℝ) - (869 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (869 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (869 / 800 : ℝ)) := by
    have h := hpThetaJensenCell869_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (85105800962307 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell869_endpointUpper :
    hpThetaJensenKernelEndpointUpper (869 / 1600 : ℝ) (87 / 160 : ℝ) ≤ (695270101 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (87 / 80 : ℝ)) (93206278856471599 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (87 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell869_product_upper
  have hD : (21023521212113 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (869 / 800 : ℝ) - (87 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell869_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell869_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (869 / 800 : ℝ) - (87 / 320 : ℝ)) ≤
      (1 / (21023521212113 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (21023521212113 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((87 / 320 : ℝ) - Real.pi * Real.exp (869 / 800 : ℝ)) ≤
      (2 / (21023521212113 / 2500000000 : ℝ) : ℝ) := by
    rw [show (87 / 320 : ℝ) - Real.pi * Real.exp (869 / 800 : ℝ) =
      -(Real.pi * Real.exp (869 / 800 : ℝ) - (87 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (93206278856471599 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (93206278856471599 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell869_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (869 / 1600 : ℝ) (87 / 160 : ℝ)) :
    (42707819 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (695270101 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell869_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell869_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell870_leftExp :
    (29668476741 / 10000000000 : ℝ) ≤ Real.exp (87 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (87 / 80 : ℝ) (1034568441469 / 1000000000000 : ℝ)
    (29668476741 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell870_rightExp :
    Real.exp (871 / 800 : ℝ) ≤ (29705585527 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (871 / 800 : ℝ) (1034608855089 / 1000000000000 : ℝ)
    (29705585527 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell870_denomUpper :
    Real.exp (90604109552524511 / 10000000000000000 : ℝ) ≤ (43038436507949 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (90604109552524511 / 10000000000000000 : ℝ) (663644052861
    / 500000000000 : ℝ) (43038436507949 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell870_denomLower :
    (17010474812181 / 2000000000 : ℝ) ≤ Real.exp (11310546772713959 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11310546772713959 / 1250000000000000 : ℝ) (663395781603
    / 500000000000 : ℝ) (17010474812181 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell870_product_lower :
    (11650781147713959 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (87 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell870_leftExp
    (by norm_num : (0 : ℝ) ≤ (29668476741 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell870_product_upper :
    Real.pi * Real.exp (871 / 800 : ℝ) ≤ (93322859552524511 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell870_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell870_endpointLower :
    (169367471 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (87 / 160 : ℝ) (871 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11650781147713959 / 1250000000000000 : ℝ) (Real.pi * Real.exp (87 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell870_product_lower
  have hD : Real.exp (Real.pi * Real.exp (871 / 800 : ℝ) - (87 / 320 : ℝ)) ≤
      (43038436507949 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell870_denomUpper
    linarith [hpThetaJensenCell870_product_upper]
  have hi : (1 / (43038436507949 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (871 / 800 : ℝ) - (87 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (43038436507949 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (43038436507949 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((87 / 320 : ℝ) - Real.pi * Real.exp (871 / 800 : ℝ)) := by
    rw [show (87 / 320 : ℝ) - Real.pi * Real.exp (871 / 800 : ℝ) =
      -(Real.pi * Real.exp (871 / 800 : ℝ) - (87 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (87 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (87 / 80 : ℝ)) := by
    have h := hpThetaJensenCell870_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (43038436507949 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell870_endpointUpper :
    hpThetaJensenKernelEndpointUpper (87 / 160 : ℝ) (871 / 1600 : ℝ) ≤ (689322323 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (871 / 800 : ℝ)) (93322859552524511 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (871 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell870_product_upper
  have hD : (17010474812181 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (87 / 80 : ℝ) - (871 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell870_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell870_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (87 / 80 : ℝ) - (871 / 3200 : ℝ)) ≤
      (1 / (17010474812181 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (17010474812181 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((871 / 3200 : ℝ) - Real.pi * Real.exp (87 / 80 : ℝ)) ≤
      (2 / (17010474812181 / 2000000000 : ℝ) : ℝ) := by
    rw [show (871 / 3200 : ℝ) - Real.pi * Real.exp (87 / 80 : ℝ) =
      -(Real.pi * Real.exp (87 / 80 : ℝ) - (871 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (93322859552524511 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (93322859552524511 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell870_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (87 / 160 : ℝ) (871 / 1600 : ℝ)) :
    (169367471 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (689322323 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell870_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell870_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell871_leftExp :
    (1188223421 / 400000000 : ℝ) ≤ Real.exp (871 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (871 / 800 : ℝ) (64663053443 / 62500000000 : ℝ)
    (1188223421 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell871_rightExp :
    Real.exp (109 / 100 : ℝ) ≤ (14871370363 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (109 / 100 : ℝ) (1034649270287 / 1000000000000 : ℝ)
    (14871370363 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell871_denomUpper :
    Real.exp (45358855532808259 / 5000000000000000 : ℝ) ≤ (43530147326047 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (45358855532808259 / 5000000000000000 : ℝ) (331939845731
    / 250000000000 : ℝ) (43530147326047 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell871_denomLower :
    (2688213630847 / 312500000 : ℝ) ≤ Real.exp (452989149203279 / 50000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (452989149203279 / 50000000000000 : ℝ) (1327262059143 /
    1000000000000 : ℝ) (2688213630847 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell871_product_lower :
    (466614149203279 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (871 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell871_leftExp
    (by norm_num : (0 : ℝ) ≤ (1188223421 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell871_product_upper :
    Real.pi * Real.exp (109 / 100 : ℝ) ≤ (46719793032808259 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell871_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell871_endpointLower :
    (335827401 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (871 / 1600 : ℝ) (109 / 200 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (466614149203279 / 50000000000000 : ℝ) (Real.pi * Real.exp (871 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell871_product_lower
  have hD : Real.exp (Real.pi * Real.exp (109 / 100 : ℝ) - (871 / 3200 : ℝ)) ≤
      (43530147326047 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell871_denomUpper
    linarith [hpThetaJensenCell871_product_upper]
  have hi : (1 / (43530147326047 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (109 / 100 : ℝ) - (871 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (43530147326047 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (43530147326047 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((871 / 3200 : ℝ) - Real.pi * Real.exp (109 / 100 : ℝ)) := by
    rw [show (871 / 3200 : ℝ) - Real.pi * Real.exp (109 / 100 : ℝ) =
      -(Real.pi * Real.exp (109 / 100 : ℝ) - (871 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (871 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (871 / 800 : ℝ)) := by
    have h := hpThetaJensenCell871_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (43530147326047 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell871_endpointUpper :
    hpThetaJensenKernelEndpointUpper (871 / 1600 : ℝ) (109 / 200 : ℝ) ≤ (683415229 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (109 / 100 : ℝ)) (46719793032808259 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (109 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell871_product_upper
  have hD : (2688213630847 / 312500000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (871 / 800 : ℝ) - (109 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell871_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell871_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (871 / 800 : ℝ) - (109 / 400 : ℝ)) ≤
      (1 / (2688213630847 / 312500000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2688213630847 / 312500000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((109 / 400 : ℝ) - Real.pi * Real.exp (871 / 800 : ℝ)) ≤
      (2 / (2688213630847 / 312500000 : ℝ) : ℝ) := by
    rw [show (109 / 400 : ℝ) - Real.pi * Real.exp (871 / 800 : ℝ) =
      -(Real.pi * Real.exp (871 / 800 : ℝ) - (109 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (46719793032808259 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (46719793032808259 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell871_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (871 / 1600 : ℝ) (109 / 200 : ℝ)) :
    (335827401 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (683415229 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell871_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell871_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell872_leftExp :
    (7435685181 / 2500000000 : ℝ) ≤ Real.exp (109 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (109 / 100 : ℝ) (517324635143 / 500000000000 : ℝ)
    (7435685181 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell872_rightExp :
    Real.exp (873 / 800 : ℝ) ≤ (29779942399 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (873 / 800 : ℝ) (129336210883 / 125000000000 : ℝ)
    (29779942399 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell872_denomUpper :
    Real.exp (90831458581101607 / 10000000000000000 : ℝ) ≤ (88056237435867 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (90831458581101607 / 10000000000000000 : ℝ) (332057858369
    / 250000000000 : ℝ) (88056237435867 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell872_denomLower :
    (87005640132301 / 10000000000 : ℝ) ≤ Real.exp (2834732228643519 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2834732228643519 / 312500000000000 : ℝ) (663866663471 /
    500000000000 : ℝ) (87005640132301 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell872_product_lower :
    (2919986134893519 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (109 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell872_leftExp
    (by norm_num : (0 : ℝ) ≤ (7435685181 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell872_product_upper :
    Real.pi * Real.exp (873 / 800 : ℝ) ≤ (93556458581101607 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell872_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell872_endpointLower :
    (332939837 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (109 / 200 : ℝ) (873 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2919986134893519 / 312500000000000 : ℝ) (Real.pi * Real.exp (109 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell872_product_lower
  have hD : Real.exp (Real.pi * Real.exp (873 / 800 : ℝ) - (109 / 400 : ℝ)) ≤
      (88056237435867 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell872_denomUpper
    linarith [hpThetaJensenCell872_product_upper]
  have hi : (1 / (88056237435867 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (873 / 800 : ℝ) - (109 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (88056237435867 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (88056237435867 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((109 / 400 : ℝ) - Real.pi * Real.exp (873 / 800 : ℝ)) := by
    rw [show (109 / 400 : ℝ) - Real.pi * Real.exp (873 / 800 : ℝ) =
      -(Real.pi * Real.exp (873 / 800 : ℝ) - (109 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (109 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (109 / 100 : ℝ)) := by
    have h := hpThetaJensenCell872_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (88056237435867 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell872_endpointUpper :
    hpThetaJensenKernelEndpointUpper (109 / 200 : ℝ) (873 / 1600 : ℝ) ≤ (135509727 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (873 / 800 : ℝ)) (93556458581101607 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (873 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell872_product_upper
  have hD : (87005640132301 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (109 / 100 : ℝ) - (873 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell872_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell872_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (109 / 100 : ℝ) - (873 / 3200 : ℝ)) ≤
      (1 / (87005640132301 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (87005640132301 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((873 / 3200 : ℝ) - Real.pi * Real.exp (109 / 100 : ℝ)) ≤
      (2 / (87005640132301 / 10000000000 : ℝ) : ℝ) := by
    rw [show (873 / 3200 : ℝ) - Real.pi * Real.exp (109 / 100 : ℝ) =
      -(Real.pi * Real.exp (109 / 100 : ℝ) - (873 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (93556458581101607 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (93556458581101607 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell872_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (109 / 200 : ℝ) (873 / 1600 : ℝ)) :
    (332939837 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (135509727 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell872_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell872_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell873_leftExp :
    (29779942397 / 10000000000 : ℝ) ≤ Real.exp (873 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (873 / 800 : ℝ) (1034689687063 / 1000000000000 : ℝ)
    (29779942397 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell873_rightExp :
    Real.exp (437 / 400 : ℝ) ≤ (14908595301 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (437 / 400 : ℝ) (1034730105419 / 1000000000000 : ℝ)
    (14908595301 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell873_denomUpper :
    Real.exp (45472676137454493 / 5000000000000000 : ℝ) ≤ (44532437711137 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (45472676137454493 / 5000000000000000 : ℝ) (265740851763
    / 200000000000 : ℝ) (44532437711137 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell873_denomLower :
    (5500059834863 / 625000000 : ℝ) ≤ Real.exp (11353147349359503 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11353147349359503 / 1250000000000000 : ℝ) (332051342019
    / 250000000000 : ℝ) (5500059834863 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell873_product_lower :
    (11694553599359503 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (873 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell873_leftExp
    (by norm_num : (0 : ℝ) ≤ (29779942397 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell873_product_upper :
    Real.pi * Real.exp (437 / 400 : ℝ) ≤ (46836738637454493 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell873_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell873_endpointLower :
    (330072159 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (873 / 1600 : ℝ) (437 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11694553599359503 / 1250000000000000 : ℝ) (Real.pi * Real.exp (873 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell873_product_lower
  have hD : Real.exp (Real.pi * Real.exp (437 / 400 : ℝ) - (873 / 3200 : ℝ)) ≤
      (44532437711137 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell873_denomUpper
    linarith [hpThetaJensenCell873_product_upper]
  have hi : (1 / (44532437711137 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (437 / 400 : ℝ) - (873 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (44532437711137 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (44532437711137 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((873 / 3200 : ℝ) - Real.pi * Real.exp (437 / 400 : ℝ)) := by
    rw [show (873 / 3200 : ℝ) - Real.pi * Real.exp (437 / 400 : ℝ) =
      -(Real.pi * Real.exp (437 / 400 : ℝ) - (873 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (873 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (873 / 800 : ℝ)) := by
    have h := hpThetaJensenCell873_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (44532437711137 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell873_endpointUpper :
    hpThetaJensenKernelEndpointUpper (873 / 1600 : ℝ) (437 / 800 : ℝ) ≤ (134344471 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (437 / 400 : ℝ)) (46836738637454493 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (437 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell873_product_upper
  have hD : (5500059834863 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (873 / 800 : ℝ) - (437 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell873_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell873_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (873 / 800 : ℝ) - (437 / 1600 : ℝ)) ≤
      (1 / (5500059834863 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5500059834863 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((437 / 1600 : ℝ) - Real.pi * Real.exp (873 / 800 : ℝ)) ≤
      (2 / (5500059834863 / 625000000 : ℝ) : ℝ) := by
    rw [show (437 / 1600 : ℝ) - Real.pi * Real.exp (873 / 800 : ℝ) =
      -(Real.pi * Real.exp (873 / 800 : ℝ) - (437 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (46836738637454493 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (46836738637454493 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell873_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (873 / 1600 : ℝ) (437 / 800 : ℝ)) :
    (330072159 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (134344471 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell873_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell873_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell874_leftExp :
    (149085953 / 50000000 : ℝ) ≤ Real.exp (437 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (437 / 400 : ℝ) (517365052709 / 500000000000 : ℝ)
    (149085953 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell874_rightExp :
    Real.exp (35 / 32 : ℝ) ≤ (14927242697 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (35 / 32 : ℝ) (1034770525353 / 1000000000000 : ℝ)
    (14927242697 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell874_denomUpper :
    Real.exp (45529696166196321 / 5000000000000000 : ℝ) ≤ (22521596338949 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (45529696166196321 / 5000000000000000 : ℝ) (1329177860419
    / 1000000000000 : ℝ) (22521596338949 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell874_denomLower :
    (17801792361871 / 2000000000 : ℝ) ≤ Real.exp (56836920282147 / 6250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (56836920282147 / 6250000000000 : ℝ) (664339091991 /
    500000000000 : ℝ) (17801792361871 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell874_product_lower :
    (58545904657147 / 6250000000000 : ℝ) ≤ Real.pi * Real.exp (437 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell874_leftExp
    (by norm_num : (0 : ℝ) ≤ (149085953 / 50000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell874_product_upper :
    Real.pi * Real.exp (35 / 32 : ℝ) ≤ (46895321166196321 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell874_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell874_endpointLower :
    (654448551 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (437 / 800 : ℝ) (35 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (58545904657147 / 6250000000000 : ℝ) (Real.pi * Real.exp (437 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell874_product_lower
  have hD : Real.exp (Real.pi * Real.exp (35 / 32 : ℝ) - (437 / 1600 : ℝ)) ≤
      (22521596338949 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell874_denomUpper
    linarith [hpThetaJensenCell874_product_upper]
  have hi : (1 / (22521596338949 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (35 / 32 : ℝ) - (437 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (22521596338949 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (22521596338949 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((437 / 1600 : ℝ) - Real.pi * Real.exp (35 / 32 : ℝ)) := by
    rw [show (437 / 1600 : ℝ) - Real.pi * Real.exp (35 / 32 : ℝ) =
      -(Real.pi * Real.exp (35 / 32 : ℝ) - (437 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (437 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (437 / 400 : ℝ)) := by
    have h := hpThetaJensenCell874_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (22521596338949 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell874_endpointUpper :
    hpThetaJensenKernelEndpointUpper (437 / 800 : ℝ) (35 / 64 : ℝ) ≤ (166484051 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (35 / 32 : ℝ)) (46895321166196321 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (35 / 64 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell874_product_upper
  have hD : (17801792361871 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (437 / 400 : ℝ) - (35 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell874_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell874_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (437 / 400 : ℝ) - (35 / 128 : ℝ)) ≤
      (1 / (17801792361871 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (17801792361871 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((35 / 128 : ℝ) - Real.pi * Real.exp (437 / 400 : ℝ)) ≤
      (2 / (17801792361871 / 2000000000 : ℝ) : ℝ) := by
    rw [show (35 / 128 : ℝ) - Real.pi * Real.exp (437 / 400 : ℝ) =
      -(Real.pi * Real.exp (437 / 400 : ℝ) - (35 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (46895321166196321 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (46895321166196321 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell874_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (437 / 800 : ℝ) (35 / 64 : ℝ)) :
    (654448551 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (166484051 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell874_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell874_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell875_leftExp :
    (1865905337 / 625000000 : ℝ) ≤ Real.exp (35 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (35 / 32 : ℝ) (129346315669 / 125000000000 : ℝ)
    (1865905337 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell875_rightExp :
    Real.exp (219 / 200 : ℝ) ≤ (5978365367 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (219 / 200 : ℝ) (517405473433 / 500000000000 : ℝ)
    (5978365367 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell875_denomUpper :
    Real.exp (18234715788409631 / 2000000000000000 : ℝ) ≤ (91120946659561 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (18234715788409631 / 2000000000000000 : ℝ) (1329652239781
    / 1000000000000 : ℝ) (91120946659561 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell875_denomLower :
    (562686438239 / 62500000 : ℝ) ≤ Real.exp (711352441184563 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (711352441184563 / 78125000000000 : ℝ) (1329151776137 /
    1000000000000 : ℝ) (562686438239 / 62500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell875_product_lower :
    (732739159934563 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (35 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell875_leftExp
    (by norm_num : (0 : ℝ) ≤ (1865905337 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell875_product_upper :
    Real.pi * Real.exp (219 / 200 : ℝ) ≤ (18781590788409631 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell875_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell875_endpointLower :
    (162198047 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (35 / 64 : ℝ) (219 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (732739159934563 / 78125000000000 : ℝ) (Real.pi * Real.exp (35 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell875_product_lower
  have hD : Real.exp (Real.pi * Real.exp (219 / 200 : ℝ) - (35 / 128 : ℝ)) ≤
      (91120946659561 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell875_denomUpper
    linarith [hpThetaJensenCell875_product_upper]
  have hi : (1 / (91120946659561 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (219 / 200 : ℝ) - (35 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (91120946659561 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (91120946659561 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((35 / 128 : ℝ) - Real.pi * Real.exp (219 / 200 : ℝ)) := by
    rw [show (35 / 128 : ℝ) - Real.pi * Real.exp (219 / 200 : ℝ) =
      -(Real.pi * Real.exp (219 / 200 : ℝ) - (35 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (35 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (35 / 32 : ℝ)) := by
    have h := hpThetaJensenCell875_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (91120946659561 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell875_endpointUpper :
    hpThetaJensenKernelEndpointUpper (35 / 64 : ℝ) (219 / 400 : ℝ) ≤ (330094999 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (219 / 200 : ℝ)) (18781590788409631 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (219 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell875_product_upper
  have hD : (562686438239 / 62500000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (35 / 32 : ℝ) - (219 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell875_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell875_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (35 / 32 : ℝ) - (219 / 800 : ℝ)) ≤
      (1 / (562686438239 / 62500000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (562686438239 / 62500000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((219 / 800 : ℝ) - Real.pi * Real.exp (35 / 32 : ℝ)) ≤
      (2 / (562686438239 / 62500000 : ℝ) : ℝ) := by
    rw [show (219 / 800 : ℝ) - Real.pi * Real.exp (35 / 32 : ℝ) =
      -(Real.pi * Real.exp (35 / 32 : ℝ) - (219 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (18781590788409631 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (18781590788409631 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell875_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (35 / 64 : ℝ) (219 / 400 : ℝ)) :
    (162198047 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (330094999 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell875_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell875_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell876_leftExp :
    (29891826833 / 10000000000 : ℝ) ≤ Real.exp (219 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (219 / 200 : ℝ) (206962189373 / 200000000000 : ℝ)
    (29891826833 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell876_rightExp :
    Real.exp (877 / 800 : ℝ) ≤ (14964607491 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (877 / 800 : ℝ) (1034851369959 / 1000000000000 : ℝ)
    (14964607491 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell876_denomUpper :
    Real.exp (45643956141473163 / 5000000000000000 : ℝ) ≤ (23042185340999 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (45643956141473163 / 5000000000000000 : ℝ) (1330127398357
    / 1000000000000 : ℝ) (23042185340999 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell876_denomLower :
    (45531870797413 / 5000000000 : ℝ) ≤ Real.exp (11395912380492267 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11395912380492267 / 1250000000000000 : ℝ) (664813073017
    / 500000000000 : ℝ) (45531870797413 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell876_product_lower :
    (11738490505492267 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (219 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell876_leftExp
    (by norm_num : (0 : ℝ) ≤ (29891826833 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell876_product_upper :
    Real.pi * Real.exp (877 / 800 : ℝ) ≤ (47012706141473163 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell876_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell876_endpointLower :
    (80396881 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (219 / 400 : ℝ) (877 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11738490505492267 / 1250000000000000 : ℝ) (Real.pi * Real.exp (219 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell876_product_lower
  have hD : Real.exp (Real.pi * Real.exp (877 / 800 : ℝ) - (219 / 800 : ℝ)) ≤
      (23042185340999 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell876_denomUpper
    linarith [hpThetaJensenCell876_product_upper]
  have hi : (1 / (23042185340999 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (877 / 800 : ℝ) - (219 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (23042185340999 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (23042185340999 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((219 / 800 : ℝ) - Real.pi * Real.exp (877 / 800 : ℝ)) := by
    rw [show (219 / 800 : ℝ) - Real.pi * Real.exp (877 / 800 : ℝ) =
      -(Real.pi * Real.exp (877 / 800 : ℝ) - (219 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (219 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (219 / 200 : ℝ)) := by
    have h := hpThetaJensenCell876_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (23042185340999 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell876_endpointUpper :
    hpThetaJensenKernelEndpointUpper (219 / 400 : ℝ) (877 / 1600 : ℝ) ≤ (20452611 / 312500000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (877 / 800 : ℝ)) (47012706141473163 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (877 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell876_product_upper
  have hD : (45531870797413 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (219 / 200 : ℝ) - (877 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell876_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell876_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (219 / 200 : ℝ) - (877 / 3200 : ℝ)) ≤
      (1 / (45531870797413 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (45531870797413 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((877 / 3200 : ℝ) - Real.pi * Real.exp (219 / 200 : ℝ)) ≤
      (2 / (45531870797413 / 5000000000 : ℝ) : ℝ) := by
    rw [show (877 / 3200 : ℝ) - Real.pi * Real.exp (219 / 200 : ℝ) =
      -(Real.pi * Real.exp (219 / 200 : ℝ) - (877 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (47012706141473163 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (47012706141473163 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell876_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (219 / 400 : ℝ) (877 / 1600 : ℝ)) :
    (80396881 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (20452611 / 312500000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell876_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell876_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell877_leftExp :
    (1496460749 / 500000000 : ℝ) ≤ Real.exp (877 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (877 / 800 : ℝ) (517425684979 / 500000000000 : ℝ)
    (1496460749 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell877_rightExp :
    Real.exp (439 / 400 : ℝ) ≤ (7491662473 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (439 / 400 : ℝ) (103489179463 / 100000000000 : ℝ)
    (7491662473 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell877_denomUpper :
    Real.exp (22850598133539489 / 2500000000000000 : ℝ) ≤ (93229954237043 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (22850598133539489 / 2500000000000000 : ℝ) (1330603337607
    / 1000000000000 : ℝ) (93229954237043 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell877_denomLower :
    (23027719539337 / 2500000000 : ℝ) ≤ Real.exp (570510202171551 / 62500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (570510202171551 / 62500000000000 : ℝ) (133010129513 /
    100000000000 : ℝ) (23027719539337 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell877_product_lower :
    (587658639671551 / 62500000000000 : ℝ) ≤ Real.pi * Real.exp (877 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell877_leftExp
    (by norm_num : (0 : ℝ) ≤ (1496460749 / 500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell877_product_upper :
    Real.pi * Real.exp (439 / 400 : ℝ) ≤ (23535754383539489 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell877_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell877_endpointLower :
    (159399237 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (877 / 1600 : ℝ) (439 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (587658639671551 / 62500000000000 : ℝ) (Real.pi * Real.exp (877 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell877_product_lower
  have hD : Real.exp (Real.pi * Real.exp (439 / 400 : ℝ) - (877 / 3200 : ℝ)) ≤
      (93229954237043 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell877_denomUpper
    linarith [hpThetaJensenCell877_product_upper]
  have hi : (1 / (93229954237043 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (439 / 400 : ℝ) - (877 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (93229954237043 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (93229954237043 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((877 / 3200 : ℝ) - Real.pi * Real.exp (439 / 400 : ℝ)) := by
    rw [show (877 / 3200 : ℝ) - Real.pi * Real.exp (439 / 400 : ℝ) =
      -(Real.pi * Real.exp (439 / 400 : ℝ) - (877 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (877 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (877 / 800 : ℝ)) := by
    have h := hpThetaJensenCell877_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (93229954237043 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell877_endpointUpper :
    hpThetaJensenKernelEndpointUpper (877 / 1600 : ℝ) (439 / 800 : ℝ) ≤ (648816681 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (439 / 400 : ℝ)) (23535754383539489 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (439 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell877_product_upper
  have hD : (23027719539337 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (877 / 800 : ℝ) - (439 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell877_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell877_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (877 / 800 : ℝ) - (439 / 1600 : ℝ)) ≤
      (1 / (23027719539337 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (23027719539337 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((439 / 1600 : ℝ) - Real.pi * Real.exp (877 / 800 : ℝ)) ≤
      (2 / (23027719539337 / 2500000000 : ℝ) : ℝ) := by
    rw [show (439 / 1600 : ℝ) - Real.pi * Real.exp (877 / 800 : ℝ) =
      -(Real.pi * Real.exp (877 / 800 : ℝ) - (439 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (23535754383539489 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (23535754383539489 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell877_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (877 / 1600 : ℝ) (439 / 800 : ℝ)) :
    (159399237 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (648816681 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell877_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell877_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell878_leftExp :
    (2996664989 / 1000000000 : ℝ) ≤ Real.exp (439 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (439 / 400 : ℝ) (1034891794629 / 1000000000000 : ℝ)
    (2996664989 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell878_rightExp :
    Real.exp (879 / 800 : ℝ) ≤ (240033053 / 80000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (879 / 800 : ℝ) (12936652761 / 12500000000 : ℝ)
    (240033053 / 80000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell878_denomUpper :
    Real.exp (732136159073429 / 80000000000000 : ℝ) ≤ (9430477290749 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (732136159073429 / 80000000000000 : ℝ) (133108005903 /
    100000000000 : ℝ) (9430477290749 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell878_denomLower :
    (93171424455457 / 10000000000 : ℝ) ≤ Real.exp (1142451407015311 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1142451407015311 / 125000000000000 : ℝ) (332644306221 /
    250000000000 : ℝ) (93171424455457 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell878_product_lower :
    (1176787344515311 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (439 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell878_leftExp
    (by norm_num : (0 : ℝ) ≤ (2996664989 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell878_product_upper :
    Real.pi * Real.exp (879 / 800 : ℝ) ≤ (754086159073429 / 80000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell878_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell878_endpointLower :
    (126411541 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (439 / 800 : ℝ) (879 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1176787344515311 / 125000000000000 : ℝ) (Real.pi * Real.exp (439 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell878_product_lower
  have hD : Real.exp (Real.pi * Real.exp (879 / 800 : ℝ) - (439 / 1600 : ℝ)) ≤
      (9430477290749 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell878_denomUpper
    linarith [hpThetaJensenCell878_product_upper]
  have hi : (1 / (9430477290749 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (879 / 800 : ℝ) - (439 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (9430477290749 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (9430477290749 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((439 / 1600 : ℝ) - Real.pi * Real.exp (879 / 800 : ℝ)) := by
    rw [show (439 / 1600 : ℝ) - Real.pi * Real.exp (879 / 800 : ℝ) =
      -(Real.pi * Real.exp (879 / 800 : ℝ) - (439 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (439 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (439 / 400 : ℝ)) := by
    have h := hpThetaJensenCell878_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (9430477290749 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell878_endpointUpper :
    hpThetaJensenKernelEndpointUpper (439 / 800 : ℝ) (879 / 1600 : ℝ) ≤ (321594601 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (879 / 800 : ℝ)) (754086159073429 / 80000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (879 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell878_product_upper
  have hD : (93171424455457 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (439 / 400 : ℝ) - (879 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell878_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell878_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (439 / 400 : ℝ) - (879 / 3200 : ℝ)) ≤
      (1 / (93171424455457 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (93171424455457 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((879 / 3200 : ℝ) - Real.pi * Real.exp (439 / 400 : ℝ)) ≤
      (2 / (93171424455457 / 10000000000 : ℝ) : ℝ) := by
    rw [show (879 / 3200 : ℝ) - Real.pi * Real.exp (439 / 400 : ℝ) =
      -(Real.pi * Real.exp (439 / 400 : ℝ) - (879 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (754086159073429 / 80000000000000 : ℝ) ^ 2 - 6 *
      (754086159073429 / 80000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell878_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (439 / 800 : ℝ) (879 / 1600 : ℝ)) :
    (126411541 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (321594601 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell878_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell878_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell879_leftExp :
    (30004131623 / 10000000000 : ℝ) ≤ Real.exp (879 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (879 / 800 : ℝ) (1034932220879 / 1000000000000 : ℝ)
    (30004131623 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell879_rightExp :
    Real.exp (11 / 10 : ℝ) ≤ (375520753 / 125000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11 / 10 : ℝ) (1034972648709 / 1000000000000 : ℝ)
    (375520753 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell879_denomUpper :
    Real.exp (1145397431479529 / 125000000000000 : ℝ) ≤ (47696693904339 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1145397431479529 / 125000000000000 : ℝ) (665778782059 /
    500000000000 : ℝ) (47696693904339 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell879_denomLower :
    (94245568002287 / 10000000000 : ℝ) ≤ Real.exp (11438842484220477 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11438842484220477 / 1250000000000000 : ℝ) (332763484199
    / 250000000000 : ℝ) (94245568002287 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell879_product_lower :
    (11782592484220477 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (879 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell879_leftExp
    (by norm_num : (0 : ℝ) ≤ (30004131623 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell879_product_upper :
    Real.pi * Real.exp (11 / 10 : ℝ) ≤ (1179733368979529 / 125000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell879_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell879_endpointLower :
    (39159821 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (879 / 1600 : ℝ) (11 / 20 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11782592484220477 / 1250000000000000 : ℝ) (Real.pi * Real.exp (879 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell879_product_lower
  have hD : Real.exp (Real.pi * Real.exp (11 / 10 : ℝ) - (879 / 3200 : ℝ)) ≤
      (47696693904339 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell879_denomUpper
    linarith [hpThetaJensenCell879_product_upper]
  have hi : (1 / (47696693904339 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (11 / 10 : ℝ) - (879 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (47696693904339 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (47696693904339 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((879 / 3200 : ℝ) - Real.pi * Real.exp (11 / 10 : ℝ)) := by
    rw [show (879 / 3200 : ℝ) - Real.pi * Real.exp (11 / 10 : ℝ) =
      -(Real.pi * Real.exp (11 / 10 : ℝ) - (879 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (879 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (879 / 800 : ℝ)) := by
    have h := hpThetaJensenCell879_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (47696693904339 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell879_endpointUpper :
    hpThetaJensenKernelEndpointUpper (879 / 1600 : ℝ) (11 / 20 : ℝ) ≤ (19925029 / 312500000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (11 / 10 : ℝ)) (1179733368979529 / 125000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (11 / 20 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell879_product_upper
  have hD : (94245568002287 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (879 / 800 : ℝ) - (11 / 40 : ℝ)) := by
    apply le_trans hpThetaJensenCell879_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell879_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (879 / 800 : ℝ) - (11 / 40 : ℝ)) ≤
      (1 / (94245568002287 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (94245568002287 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((11 / 40 : ℝ) - Real.pi * Real.exp (879 / 800 : ℝ)) ≤
      (2 / (94245568002287 / 10000000000 : ℝ) : ℝ) := by
    rw [show (11 / 40 : ℝ) - Real.pi * Real.exp (879 / 800 : ℝ) =
      -(Real.pi * Real.exp (879 / 800 : ℝ) - (11 / 40 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1179733368979529 / 125000000000000 : ℝ) ^ 2 - 6 *
      (1179733368979529 / 125000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell879_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (879 / 1600 : ℝ) (11 / 20 : ℝ)) :
    (39159821 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (19925029 / 312500000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell879_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell879_endpointUpper

def hpThetaJensenCellsBatch043Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (737858557 / 10000000000 : ℝ)
  | 1 => (9145423 / 125000000 : ℝ)
  | 2 => (22670341 / 312500000 : ℝ)
  | 3 => (71930959 / 1000000000 : ℝ)
  | 4 => (71320969 / 1000000000 : ℝ)
  | 5 => (70715103 / 1000000000 : ℝ)
  | 6 => (43820839 / 625000000 : ℝ)
  | 7 => (695156691 / 10000000000 : ℝ)
  | 8 => (137844129 / 2000000000 : ℝ)
  | 9 => (42707819 / 625000000 : ℝ)
  | 10 => (169367471 / 2500000000 : ℝ)
  | 11 => (335827401 / 5000000000 : ℝ)
  | 12 => (332939837 / 5000000000 : ℝ)
  | 13 => (330072159 / 5000000000 : ℝ)
  | 14 => (654448551 / 10000000000 : ℝ)
  | 15 => (162198047 / 2500000000 : ℝ)
  | 16 => (80396881 / 1250000000 : ℝ)
  | 17 => (159399237 / 2500000000 : ℝ)
  | 18 => (126411541 / 2000000000 : ℝ)
  | 19 => (39159821 / 625000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch043Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (750661463 / 10000000000 : ℝ)
  | 1 => (744339189 / 10000000000 : ℝ)
  | 2 => (184514817 / 2500000000 : ℝ)
  | 3 => (91477689 / 1250000000 : ℝ)
  | 4 => (725625739 / 10000000000 : ℝ)
  | 5 => (719471761 / 10000000000 : ℝ)
  | 6 => (713359393 / 10000000000 : ℝ)
  | 7 => (707288451 / 10000000000 : ℝ)
  | 8 => (701258749 / 10000000000 : ℝ)
  | 9 => (695270101 / 10000000000 : ℝ)
  | 10 => (689322323 / 10000000000 : ℝ)
  | 11 => (683415229 / 10000000000 : ℝ)
  | 12 => (135509727 / 2000000000 : ℝ)
  | 13 => (134344471 / 2000000000 : ℝ)
  | 14 => (166484051 / 2500000000 : ℝ)
  | 15 => (330094999 / 5000000000 : ℝ)
  | 16 => (20452611 / 312500000 : ℝ)
  | 17 => (648816681 / 10000000000 : ℝ)
  | 18 => (321594601 / 5000000000 : ℝ)
  | 19 => (19925029 / 312500000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch043_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((860 : ℝ) + (j.val : ℝ)) / 1600)
      (((860 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch043Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch043Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell860_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell861_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell862_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell863_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell864_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell865_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell866_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell867_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell868_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell869_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell870_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell871_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell872_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell873_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell874_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell875_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell876_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell877_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell878_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell879_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper] at h ⊢
    exact h

end HodgeProofHP
