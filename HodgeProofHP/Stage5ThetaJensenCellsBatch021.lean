import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell420_leftExp :
    (16904588483 / 10000000000 : ℝ) ≤ Real.exp (21 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (21 / 40 : ℝ) (508270785773 / 500000000000 : ℝ)
    (16904588483 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell420_rightExp :
    Real.exp (421 / 800 : ℝ) ≤ (16925732433 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (421 / 800 : ℝ) (508290640489 / 500000000000 : ℝ)
    (16925732433 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell420_denomUpper :
    Real.exp (51861262531385769 / 10000000000000000 : ℝ) ≤ (446936704999 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (51861262531385769 / 10000000000000000 : ℝ) (587969187217
    / 500000000000 : ℝ) (446936704999 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell420_denomLower :
    (14202824451 / 80000000 : ℝ) ≤ Real.exp (6473961867685617 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6473961867685617 / 1250000000000000 : ℝ) (293920688681 /
    250000000000 : ℝ) (14202824451 / 80000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell420_product_lower :
    (6638414992685617 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (21 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell420_leftExp
    (by norm_num : (0 : ℝ) ≤ (16904588483 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell420_product_upper :
    Real.pi * Real.exp (421 / 800 : ℝ) ≤ (53173762531385769 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell420_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell420_endpointLower :
    (9056215833 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (21 / 80 : ℝ) (421 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6638414992685617 / 1250000000000000 : ℝ) (Real.pi * Real.exp (21 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell420_product_lower
  have hD : Real.exp (Real.pi * Real.exp (421 / 800 : ℝ) - (21 / 160 : ℝ)) ≤
      (446936704999 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell420_denomUpper
    linarith [hpThetaJensenCell420_product_upper]
  have hi : (1 / (446936704999 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (421 / 800 : ℝ) - (21 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (446936704999 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (446936704999 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((21 / 160 : ℝ) - Real.pi * Real.exp (421 / 800 : ℝ)) := by
    rw [show (21 / 160 : ℝ) - Real.pi * Real.exp (421 / 800 : ℝ) =
      -(Real.pi * Real.exp (421 / 800 : ℝ) - (21 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (21 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (21 / 40 : ℝ)) := by
    have h := hpThetaJensenCell420_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (446936704999 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell420_endpointUpper :
    hpThetaJensenKernelEndpointUpper (21 / 80 : ℝ) (421 / 1600 : ℝ) ≤ (1146356903 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (421 / 800 : ℝ)) (53173762531385769 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (421 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell420_product_upper
  have hD : (14202824451 / 80000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (21 / 40 : ℝ) - (421 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell420_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell420_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (21 / 40 : ℝ) - (421 / 3200 : ℝ)) ≤
      (1 / (14202824451 / 80000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (14202824451 / 80000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((421 / 3200 : ℝ) - Real.pi * Real.exp (21 / 40 : ℝ)) ≤
      (2 / (14202824451 / 80000000 : ℝ) : ℝ) := by
    rw [show (421 / 3200 : ℝ) - Real.pi * Real.exp (21 / 40 : ℝ) =
      -(Real.pi * Real.exp (21 / 40 : ℝ) - (421 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (53173762531385769 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (53173762531385769 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell420_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (21 / 80 : ℝ) (421 / 1600 : ℝ)) :
    (9056215833 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1146356903 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell420_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell420_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell421_leftExp :
    (16925732431 / 10000000000 : ℝ) ≤ Real.exp (421 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (421 / 800 : ℝ) (1016581280977 / 1000000000000 : ℝ)
    (16925732431 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell421_rightExp :
    Real.exp (211 / 400 : ℝ) ≤ (8473451413 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (211 / 400 : ℝ) (1016620991959 / 1000000000000 : ℝ)
    (8473451413 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell421_denomUpper :
    Real.exp (25962323144920909 / 5000000000000000 : ℝ) ≤ (1799114218601 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (25962323144920909 / 5000000000000000 : ℝ) (1176171320609
    / 1000000000000 : ℝ) (1799114218601 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell421_denomLower :
    (1786626802147 / 10000000000 : ℝ) ≤ Real.exp (6481874449921269 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6481874449921269 / 1250000000000000 : ℝ) (117591534489 /
    100000000000 : ℝ) (1786626802147 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell421_product_lower :
    (6646718199921269 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (421 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell421_leftExp
    (by norm_num : (0 : ℝ) ≤ (16925732431 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell421_product_upper :
    Real.pi * Real.exp (211 / 400 : ℝ) ≤ (26620135644920909 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell421_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell421_endpointLower :
    (45129787 / 50000000 : ℝ) ≤ hpThetaTraceEndpointLower (421 / 1600 : ℝ) (211 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6646718199921269 / 1250000000000000 : ℝ) (Real.pi * Real.exp (421 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell421_product_lower
  have hD : Real.exp (Real.pi * Real.exp (211 / 400 : ℝ) - (421 / 3200 : ℝ)) ≤
      (1799114218601 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell421_denomUpper
    linarith [hpThetaJensenCell421_product_upper]
  have hi : (1 / (1799114218601 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (211 / 400 : ℝ) - (421 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1799114218601 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1799114218601 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((421 / 3200 : ℝ) - Real.pi * Real.exp (211 / 400 : ℝ)) := by
    rw [show (421 / 3200 : ℝ) - Real.pi * Real.exp (211 / 400 : ℝ) =
      -(Real.pi * Real.exp (211 / 400 : ℝ) - (421 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (421 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (421 / 800 : ℝ)) := by
    have h := hpThetaJensenCell421_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1799114218601 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell421_endpointUpper :
    hpThetaJensenKernelEndpointUpper (421 / 1600 : ℝ) (211 / 800 : ℝ) ≤ (1828056379 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (211 / 400 : ℝ)) (26620135644920909 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (211 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell421_product_upper
  have hD : (1786626802147 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (421 / 800 : ℝ) - (211 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell421_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell421_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (421 / 800 : ℝ) - (211 / 1600 : ℝ)) ≤
      (1 / (1786626802147 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1786626802147 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((211 / 1600 : ℝ) - Real.pi * Real.exp (421 / 800 : ℝ)) ≤
      (2 / (1786626802147 / 10000000000 : ℝ) : ℝ) := by
    rw [show (211 / 1600 : ℝ) - Real.pi * Real.exp (421 / 800 : ℝ) =
      -(Real.pi * Real.exp (421 / 800 : ℝ) - (211 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (26620135644920909 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (26620135644920909 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell421_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (421 / 1600 : ℝ) (211 / 800 : ℝ)) :
    (45129787 / 50000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1828056379 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell421_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell421_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell422_leftExp :
    (677876113 / 400000000 : ℝ) ≤ Real.exp (211 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (211 / 400 : ℝ) (508310495979 / 500000000000 : ℝ)
    (677876113 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell422_rightExp :
    Real.exp (423 / 800 : ℝ) ≤ (16968099701 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (423 / 800 : ℝ) (1016660704493 / 1000000000000 : ℝ)
    (16968099701 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell422_denomUpper :
    Real.exp (51988113243963693 / 10000000000000000 : ℝ) ≤ (1810568959991 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (51988113243963693 / 10000000000000000 : ℝ)
    (1176404618779 / 1000000000000 : ℝ) (1810568959991 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell422_denomLower :
    (449496768971 / 2500000000 : ℝ) ≤ Real.exp (259591896698987 / 50000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (259591896698987 / 50000000000000 : ℝ) (1176148286437 /
    1000000000000 : ℝ) (449496768971 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell422_product_lower :
    (266201271698987 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (211 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell422_leftExp
    (by norm_num : (0 : ℝ) ≤ (677876113 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell422_product_upper :
    Real.pi * Real.exp (423 / 800 : ℝ) ≤ (53306863243963693 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell422_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell422_endpointLower :
    (2248929383 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (211 / 800 : ℝ) (423 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (266201271698987 / 50000000000000 : ℝ) (Real.pi * Real.exp (211 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell422_product_lower
  have hD : Real.exp (Real.pi * Real.exp (423 / 800 : ℝ) - (211 / 1600 : ℝ)) ≤
      (1810568959991 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell422_denomUpper
    linarith [hpThetaJensenCell422_product_upper]
  have hi : (1 / (1810568959991 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (423 / 800 : ℝ) - (211 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1810568959991 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1810568959991 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((211 / 1600 : ℝ) - Real.pi * Real.exp (423 / 800 : ℝ)) := by
    rw [show (211 / 1600 : ℝ) - Real.pi * Real.exp (423 / 800 : ℝ) =
      -(Real.pi * Real.exp (423 / 800 : ℝ) - (211 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (211 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (211 / 400 : ℝ)) := by
    have h := hpThetaJensenCell422_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1810568959991 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell422_endpointUpper :
    hpThetaJensenKernelEndpointUpper (211 / 800 : ℝ) (423 / 1600 : ℝ) ≤ (4554863517 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (423 / 800 : ℝ)) (53306863243963693 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (423 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell422_product_upper
  have hD : (449496768971 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (211 / 400 : ℝ) - (423 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell422_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell422_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (211 / 400 : ℝ) - (423 / 3200 : ℝ)) ≤
      (1 / (449496768971 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (449496768971 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((423 / 3200 : ℝ) - Real.pi * Real.exp (211 / 400 : ℝ)) ≤
      (2 / (449496768971 / 2500000000 : ℝ) : ℝ) := by
    rw [show (423 / 3200 : ℝ) - Real.pi * Real.exp (211 / 400 : ℝ) =
      -(Real.pi * Real.exp (211 / 400 : ℝ) - (423 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (53306863243963693 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (53306863243963693 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell422_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (211 / 800 : ℝ) (423 / 1600 : ℝ)) :
    (2248929383 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4554863517 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell422_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell422_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell423_leftExp :
    (16968099699 / 10000000000 : ℝ) ≤ Real.exp (423 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (423 / 800 : ℝ) (254165176123 / 250000000000 : ℝ)
    (16968099699 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell423_rightExp :
    Real.exp (53 / 100 : ℝ) ≤ (16989323087 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (53 / 100 : ℝ) (1016700418577 / 1000000000000 : ℝ)
    (16989323087 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell423_denomUpper :
    Real.exp (52051663484857591 / 10000000000000000 : ℝ) ≤ (911055904033 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (52051663484857591 / 10000000000000000 : ℝ) (117663826947
    / 100000000000 : ℝ) (911055904033 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell423_denomLower :
    (1809434636509 / 10000000000 : ℝ) ≤ Real.exp (6497730783697601 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6497730783697601 / 1250000000000000 : ℝ) (1176381579949
    / 1000000000000 : ℝ) (1809434636509 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell423_product_lower :
    (6663355783697601 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (423 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell423_leftExp
    (by norm_num : (0 : ℝ) ≤ (16968099699 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell423_product_upper :
    Real.pi * Real.exp (53 / 100 : ℝ) ≤ (53373538484857591 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell423_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell423_endpointLower :
    (1793099331 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (423 / 1600 : ℝ) (53 / 200 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6663355783697601 / 1250000000000000 : ℝ) (Real.pi * Real.exp (423 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell423_product_lower
  have hD : Real.exp (Real.pi * Real.exp (53 / 100 : ℝ) - (423 / 3200 : ℝ)) ≤
      (911055904033 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell423_denomUpper
    linarith [hpThetaJensenCell423_product_upper]
  have hi : (1 / (911055904033 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (53 / 100 : ℝ) - (423 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (911055904033 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (911055904033 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((423 / 3200 : ℝ) - Real.pi * Real.exp (53 / 100 : ℝ)) := by
    rw [show (423 / 3200 : ℝ) - Real.pi * Real.exp (53 / 100 : ℝ) =
      -(Real.pi * Real.exp (53 / 100 : ℝ) - (423 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (423 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (423 / 800 : ℝ)) := by
    have h := hpThetaJensenCell423_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (911055904033 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell423_endpointUpper :
    hpThetaJensenKernelEndpointUpper (423 / 1600 : ℝ) (53 / 200 : ℝ) ≤ (2269797763 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (53 / 100 : ℝ)) (53373538484857591 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (53 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell423_product_upper
  have hD : (1809434636509 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (423 / 800 : ℝ) - (53 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell423_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell423_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (423 / 800 : ℝ) - (53 / 400 : ℝ)) ≤
      (1 / (1809434636509 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1809434636509 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((53 / 400 : ℝ) - Real.pi * Real.exp (423 / 800 : ℝ)) ≤
      (2 / (1809434636509 / 10000000000 : ℝ) : ℝ) := by
    rw [show (53 / 400 : ℝ) - Real.pi * Real.exp (423 / 800 : ℝ) =
      -(Real.pi * Real.exp (423 / 800 : ℝ) - (53 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (53373538484857591 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (53373538484857591 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell423_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (423 / 1600 : ℝ) (53 / 200 : ℝ)) :
    (1793099331 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2269797763 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell423_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell423_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell424_leftExp :
    (3397864617 / 2000000000 : ℝ) ≤ Real.exp (53 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (53 / 100 : ℝ) (63543776161 / 62500000000 : ℝ)
    (3397864617 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell424_rightExp :
    Real.exp (17 / 32 : ℝ) ≤ (17010573019 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (17 / 32 : ℝ) (1016740134213 / 1000000000000 : ℝ)
    (17010573019 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell424_denomUpper :
    Real.exp (52115297122479267 / 10000000000000000 : ℝ) ≤ (916871768763 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (52115297122479267 / 10000000000000000 : ℝ)
    (1176872273277 / 1000000000000 : ℝ) (916871768763 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell424_denomLower :
    (56905320283 / 312500000 : ℝ) ≤ Real.exp (1301134912231283 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1301134912231283 / 250000000000000 : ℝ) (235323045197 /
    200000000000 : ℝ) (56905320283 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell424_product_lower :
    (1334338037231283 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (53 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell424_leftExp
    (by norm_num : (0 : ℝ) ≤ (3397864617 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell424_product_upper :
    Real.pi * Real.exp (17 / 32 : ℝ) ≤ (53440297122479267 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell424_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell424_endpointLower :
    (8935295179 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (53 / 200 : ℝ) (17 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1334338037231283 / 250000000000000 : ℝ) (Real.pi * Real.exp (53 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell424_product_lower
  have hD : Real.exp (Real.pi * Real.exp (17 / 32 : ℝ) - (53 / 400 : ℝ)) ≤
      (916871768763 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell424_denomUpper
    linarith [hpThetaJensenCell424_product_upper]
  have hi : (1 / (916871768763 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (17 / 32 : ℝ) - (53 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (916871768763 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (916871768763 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((53 / 400 : ℝ) - Real.pi * Real.exp (17 / 32 : ℝ)) := by
    rw [show (53 / 400 : ℝ) - Real.pi * Real.exp (17 / 32 : ℝ) =
      -(Real.pi * Real.exp (17 / 32 : ℝ) - (53 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (53 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (53 / 100 : ℝ)) := by
    have h := hpThetaJensenCell424_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (916871768763 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell424_endpointUpper :
    hpThetaJensenKernelEndpointUpper (53 / 200 : ℝ) (17 / 64 : ℝ) ≤ (4524337187 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (17 / 32 : ℝ)) (53440297122479267 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (17 / 64 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell424_product_upper
  have hD : (56905320283 / 312500000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (53 / 100 : ℝ) - (17 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell424_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell424_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (53 / 100 : ℝ) - (17 / 128 : ℝ)) ≤
      (1 / (56905320283 / 312500000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (56905320283 / 312500000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((17 / 128 : ℝ) - Real.pi * Real.exp (53 / 100 : ℝ)) ≤
      (2 / (56905320283 / 312500000 : ℝ) : ℝ) := by
    rw [show (17 / 128 : ℝ) - Real.pi * Real.exp (53 / 100 : ℝ) =
      -(Real.pi * Real.exp (53 / 100 : ℝ) - (17 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (53440297122479267 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (53440297122479267 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell424_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (53 / 200 : ℝ) (17 / 64 : ℝ)) :
    (8935295179 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4524337187 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell424_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell424_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell425_leftExp :
    (8505286509 / 5000000000 : ℝ) ≤ Real.exp (17 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (17 / 32 : ℝ) (254185033553 / 250000000000 : ℝ)
    (8505286509 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell425_rightExp :
    Real.exp (213 / 400 : ℝ) ≤ (17031849531 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (213 / 400 : ℝ) (5083899257 / 5000000000 : ℝ)
    (17031849531 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell425_denomUpper :
    Real.exp (52179014263642883 / 10000000000000000 : ℝ) ≤ (369092986019 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (52179014263642883 / 10000000000000000 : ℝ) (235421326157
    / 200000000000 : ℝ) (369092986019 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell425_denomLower :
    (1832594687899 / 10000000000 : ℝ) ≤ Real.exp (3256814381797791 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3256814381797791 / 625000000000000 : ℝ) (1176849225143 /
    1000000000000 : ℝ) (1832594687899 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell425_product_lower :
    (3340017506797791 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (17 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell425_leftExp
    (by norm_num : (0 : ℝ) ≤ (8505286509 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell425_product_upper :
    Real.pi * Real.exp (213 / 400 : ℝ) ≤ (53507139263642883 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell425_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell425_endpointLower :
    (1781022703 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (17 / 64 : ℝ) (213 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3340017506797791 / 625000000000000 : ℝ) (Real.pi * Real.exp (17 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell425_product_lower
  have hD : Real.exp (Real.pi * Real.exp (213 / 400 : ℝ) - (17 / 128 : ℝ)) ≤
      (369092986019 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell425_denomUpper
    linarith [hpThetaJensenCell425_product_upper]
  have hi : (1 / (369092986019 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (213 / 400 : ℝ) - (17 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (369092986019 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (369092986019 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((17 / 128 : ℝ) - Real.pi * Real.exp (213 / 400 : ℝ)) := by
    rw [show (17 / 128 : ℝ) - Real.pi * Real.exp (213 / 400 : ℝ) =
      -(Real.pi * Real.exp (213 / 400 : ℝ) - (17 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (17 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (17 / 32 : ℝ)) := by
    have h := hpThetaJensenCell425_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (369092986019 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell425_endpointUpper :
    hpThetaJensenKernelEndpointUpper (17 / 64 : ℝ) (213 / 800 : ℝ) ≤ (9018177413 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (213 / 400 : ℝ)) (53507139263642883 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (213 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell425_product_upper
  have hD : (1832594687899 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (17 / 32 : ℝ) - (213 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell425_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell425_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (17 / 32 : ℝ) - (213 / 1600 : ℝ)) ≤
      (1 / (1832594687899 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1832594687899 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((213 / 1600 : ℝ) - Real.pi * Real.exp (17 / 32 : ℝ)) ≤
      (2 / (1832594687899 / 10000000000 : ℝ) : ℝ) := by
    rw [show (213 / 1600 : ℝ) - Real.pi * Real.exp (17 / 32 : ℝ) =
      -(Real.pi * Real.exp (17 / 32 : ℝ) - (213 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (53507139263642883 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (53507139263642883 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell425_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (17 / 64 : ℝ) (213 / 800 : ℝ)) :
    (1781022703 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (9018177413 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell425_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell425_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell426_leftExp :
    (17031849529 / 10000000000 : ℝ) ≤ Real.exp (213 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (213 / 400 : ℝ) (1016779851399 / 1000000000000 : ℝ)
    (17031849529 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell426_rightExp :
    Real.exp (427 / 800 : ℝ) ≤ (8526576327 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (427 / 800 : ℝ) (1016819570139 / 1000000000000 : ℝ)
    (8526576327 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell426_denomUpper :
    Real.exp (26121407502868911 / 5000000000000000 : ℝ) ≤ (1857276773471 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (26121407502868911 / 5000000000000000 : ℝ) (1177341342547
    / 1000000000000 : ℝ) (1857276773471 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell426_denomLower :
    (1844308732479 / 10000000000 : ℝ) ≤ Real.exp (6521593403188771 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6521593403188771 / 1250000000000000 : ℝ) (294270894493 /
    250000000000 : ℝ) (1844308732479 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell426_product_lower :
    (6688390278188771 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (213 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell426_leftExp
    (by norm_num : (0 : ℝ) ≤ (17031849529 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell426_product_upper :
    Real.pi * Real.exp (427 / 800 : ℝ) ≤ (26787032502868911 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell426_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell426_endpointLower :
    (8874952079 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (213 / 800 : ℝ) (427 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6688390278188771 / 1250000000000000 : ℝ) (Real.pi * Real.exp (213 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell426_product_lower
  have hD : Real.exp (Real.pi * Real.exp (427 / 800 : ℝ) - (213 / 1600 : ℝ)) ≤
      (1857276773471 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell426_denomUpper
    linarith [hpThetaJensenCell426_product_upper]
  have hi : (1 / (1857276773471 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (427 / 800 : ℝ) - (213 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1857276773471 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1857276773471 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((213 / 1600 : ℝ) - Real.pi * Real.exp (427 / 800 : ℝ)) := by
    rw [show (213 / 1600 : ℝ) - Real.pi * Real.exp (427 / 800 : ℝ) =
      -(Real.pi * Real.exp (427 / 800 : ℝ) - (213 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (213 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (213 / 400 : ℝ)) := by
    have h := hpThetaJensenCell426_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1857276773471 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell426_endpointUpper :
    hpThetaJensenKernelEndpointUpper (213 / 800 : ℝ) (427 / 1600 : ℝ) ≤ (8987700589 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (427 / 800 : ℝ)) (26787032502868911 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (427 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell426_product_upper
  have hD : (1844308732479 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (213 / 400 : ℝ) - (427 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell426_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell426_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (213 / 400 : ℝ) - (427 / 3200 : ℝ)) ≤
      (1 / (1844308732479 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1844308732479 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((427 / 3200 : ℝ) - Real.pi * Real.exp (213 / 400 : ℝ)) ≤
      (2 / (1844308732479 / 10000000000 : ℝ) : ℝ) := by
    rw [show (427 / 3200 : ℝ) - Real.pi * Real.exp (213 / 400 : ℝ) =
      -(Real.pi * Real.exp (213 / 400 : ℝ) - (427 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (26787032502868911 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (26787032502868911 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell426_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (213 / 800 : ℝ) (427 / 1600 : ℝ)) :
    (8874952079 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8987700589 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell426_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell426_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell427_leftExp :
    (17053152653 / 10000000000 : ℝ) ≤ Real.exp (427 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (427 / 800 : ℝ) (508409785069 / 500000000000 : ℝ)
    (17053152653 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell427_rightExp :
    Real.exp (107 / 200 : ℝ) ≤ (17074482423 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (107 / 200 : ℝ) (1016859290429 / 1000000000000 : ℝ)
    (17074482423 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell427_denomUpper :
    Real.exp (52306699458719839 / 10000000000000000 : ℝ) ≤ (116823741573 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (52306699458719839 / 10000000000000000 : ℝ)
    (1177576409159 / 1000000000000 : ℝ) (116823741573 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell427_denomLower :
    (7424452689 / 40000000 : ℝ) ≤ Real.exp (6529568493680447 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6529568493680447 / 1250000000000000 : ℝ) (117731828507 /
    100000000000 : ℝ) (7424452689 / 40000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell427_product_lower :
    (6696755993680447 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (427 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell427_leftExp
    (by norm_num : (0 : ℝ) ≤ (17053152653 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell427_product_upper :
    Real.pi * Real.exp (107 / 200 : ℝ) ≤ (53641074458719839 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell427_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell427_endpointLower :
    (8844811279 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (427 / 1600 : ℝ) (107 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6696755993680447 / 1250000000000000 : ℝ) (Real.pi * Real.exp (427 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell427_product_lower
  have hD : Real.exp (Real.pi * Real.exp (107 / 200 : ℝ) - (427 / 3200 : ℝ)) ≤
      (116823741573 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell427_denomUpper
    linarith [hpThetaJensenCell427_product_upper]
  have hi : (1 / (116823741573 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (107 / 200 : ℝ) - (427 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (116823741573 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (116823741573 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((427 / 3200 : ℝ) - Real.pi * Real.exp (107 / 200 : ℝ)) := by
    rw [show (427 / 3200 : ℝ) - Real.pi * Real.exp (107 / 200 : ℝ) =
      -(Real.pi * Real.exp (107 / 200 : ℝ) - (427 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (427 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (427 / 800 : ℝ)) := by
    have h := hpThetaJensenCell427_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (116823741573 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell427_endpointUpper :
    hpThetaJensenKernelEndpointUpper (427 / 1600 : ℝ) (107 / 400 : ℝ) ≤ (1119655539 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (107 / 200 : ℝ)) (53641074458719839 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (107 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell427_product_upper
  have hD : (7424452689 / 40000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (427 / 800 : ℝ) - (107 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell427_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell427_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (427 / 800 : ℝ) - (107 / 800 : ℝ)) ≤
      (1 / (7424452689 / 40000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (7424452689 / 40000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((107 / 800 : ℝ) - Real.pi * Real.exp (427 / 800 : ℝ)) ≤
      (2 / (7424452689 / 40000000 : ℝ) : ℝ) := by
    rw [show (107 / 800 : ℝ) - Real.pi * Real.exp (427 / 800 : ℝ) =
      -(Real.pi * Real.exp (427 / 800 : ℝ) - (107 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (53641074458719839 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (53641074458719839 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell427_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (427 / 1600 : ℝ) (107 / 400 : ℝ)) :
    (8844811279 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1119655539 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell427_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell427_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell428_leftExp :
    (8537241211 / 5000000000 : ℝ) ≤ Real.exp (107 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (107 / 200 : ℝ) (254214822607 / 250000000000 : ℝ)
    (8537241211 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell428_rightExp :
    Real.exp (429 / 800 : ℝ) ≤ (17095838871 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (429 / 800 : ℝ) (1016899012271 / 1000000000000 : ℝ)
    (17095838871 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell428_denomUpper :
    Real.exp (52370667726261503 / 10000000000000000 : ℝ) ≤ (470293752373 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (52370667726261503 / 10000000000000000 : ℝ) (588905915599
    / 500000000000 : ℝ) (470293752373 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell428_denomLower :
    (934004401311 / 5000000000 : ℝ) ≤ Real.exp (3268777023818489 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3268777023818489 / 625000000000000 : ℝ) (1177553347001 /
    1000000000000 : ℝ) (934004401311 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell428_product_lower :
    (3352566086318489 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (107 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell428_leftExp
    (by norm_num : (0 : ℝ) ≤ (8537241211 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell428_product_upper :
    Real.pi * Real.exp (429 / 800 : ℝ) ≤ (53708167726261503 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell428_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell428_endpointLower :
    (8814691523 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (107 / 400 : ℝ) (429 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3352566086318489 / 625000000000000 : ℝ) (Real.pi * Real.exp (107 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell428_product_lower
  have hD : Real.exp (Real.pi * Real.exp (429 / 800 : ℝ) - (107 / 800 : ℝ)) ≤
      (470293752373 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell428_denomUpper
    linarith [hpThetaJensenCell428_product_upper]
  have hi : (1 / (470293752373 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (429 / 800 : ℝ) - (107 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (470293752373 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (470293752373 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((107 / 800 : ℝ) - Real.pi * Real.exp (429 / 800 : ℝ)) := by
    rw [show (107 / 800 : ℝ) - Real.pi * Real.exp (429 / 800 : ℝ) =
      -(Real.pi * Real.exp (429 / 800 : ℝ) - (107 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (107 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (107 / 200 : ℝ)) := by
    have h := hpThetaJensenCell428_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (470293752373 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell428_endpointUpper :
    hpThetaJensenKernelEndpointUpper (107 / 400 : ℝ) (429 / 1600 : ℝ) ≤ (8926809001 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (429 / 800 : ℝ)) (53708167726261503 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (429 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell428_product_upper
  have hD : (934004401311 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (107 / 200 : ℝ) - (429 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell428_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell428_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (107 / 200 : ℝ) - (429 / 3200 : ℝ)) ≤
      (1 / (934004401311 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (934004401311 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((429 / 3200 : ℝ) - Real.pi * Real.exp (107 / 200 : ℝ)) ≤
      (2 / (934004401311 / 5000000000 : ℝ) : ℝ) := by
    rw [show (429 / 3200 : ℝ) - Real.pi * Real.exp (107 / 200 : ℝ) =
      -(Real.pi * Real.exp (107 / 200 : ℝ) - (429 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (53708167726261503 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (53708167726261503 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell428_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (107 / 400 : ℝ) (429 / 1600 : ℝ)) :
    (8814691523 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8926809001 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell428_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell428_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell429_leftExp :
    (1709583887 / 1000000000 : ℝ) ≤ Real.exp (429 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (429 / 800 : ℝ) (101689901227 / 100000000000 : ℝ)
    (1709583887 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell429_rightExp :
    Real.exp (43 / 80 : ℝ) ≤ (17117222031 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (43 / 80 : ℝ) (63558670979 / 62500000000 : ℝ)
    (17117222031 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell429_denomUpper :
    Real.exp (52434719912035383 / 10000000000000000 : ℝ) ≤ (946631509209 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (52434719912035383 / 10000000000000000 : ℝ) (589023804619
    / 500000000000 : ℝ) (946631509209 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell429_denomLower :
    (469999106949 / 2500000000 : ℝ) ≤ Real.exp (654555007841013 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (654555007841013 / 125000000000000 : ℝ) (23555775287 /
    20000000000 : ℝ) (469999106949 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell429_product_lower :
    (671351882841013 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (429 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell429_leftExp
    (by norm_num : (0 : ℝ) ≤ (1709583887 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell429_product_upper :
    Real.pi * Real.exp (43 / 80 : ℝ) ≤ (53775344912035383 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell429_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell429_endpointLower :
    (8784593219 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (429 / 1600 : ℝ) (43 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (671351882841013 / 125000000000000 : ℝ) (Real.pi * Real.exp (429 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell429_product_lower
  have hD : Real.exp (Real.pi * Real.exp (43 / 80 : ℝ) - (429 / 3200 : ℝ)) ≤
      (946631509209 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell429_denomUpper
    linarith [hpThetaJensenCell429_product_upper]
  have hi : (1 / (946631509209 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (43 / 80 : ℝ) - (429 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (946631509209 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (946631509209 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((429 / 3200 : ℝ) - Real.pi * Real.exp (43 / 80 : ℝ)) := by
    rw [show (429 / 3200 : ℝ) - Real.pi * Real.exp (43 / 80 : ℝ) =
      -(Real.pi * Real.exp (43 / 80 : ℝ) - (429 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (429 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (429 / 800 : ℝ)) := by
    have h := hpThetaJensenCell429_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (946631509209 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell429_endpointUpper :
    hpThetaJensenKernelEndpointUpper (429 / 1600 : ℝ) (43 / 160 : ℝ) ≤ (1779279013 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (43 / 80 : ℝ)) (53775344912035383 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (43 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell429_product_upper
  have hD : (469999106949 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (429 / 800 : ℝ) - (43 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell429_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell429_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (429 / 800 : ℝ) - (43 / 320 : ℝ)) ≤
      (1 / (469999106949 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (469999106949 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((43 / 320 : ℝ) - Real.pi * Real.exp (429 / 800 : ℝ)) ≤
      (2 / (469999106949 / 2500000000 : ℝ) : ℝ) := by
    rw [show (43 / 320 : ℝ) - Real.pi * Real.exp (429 / 800 : ℝ) =
      -(Real.pi * Real.exp (429 / 800 : ℝ) - (43 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (53775344912035383 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (53775344912035383 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell429_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (429 / 1600 : ℝ) (43 / 160 : ℝ)) :
    (8784593219 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1779279013 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell429_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell429_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell430_leftExp :
    (1711722203 / 1000000000 : ℝ) ≤ Real.exp (43 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (43 / 80 : ℝ) (1016938735663 / 1000000000000 : ℝ)
    (1711722203 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell430_rightExp :
    Real.exp (431 / 800 : ℝ) ≤ (8569315969 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (431 / 800 : ℝ) (101697846061 / 100000000000 : ℝ)
    (8569315969 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell430_denomUpper :
    Real.exp (26249428062998617 / 5000000000000000 : ℝ) ≤ (1905444713269 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (26249428062998617 / 5000000000000000 : ℝ) (1178283743881
    / 1000000000000 : ℝ) (1905444713269 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell430_denomLower :
    (189207685939 / 1000000000 : ℝ) ≤ Real.exp (655355659895897 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (655355659895897 / 125000000000000 : ℝ) (589012268847 /
    500000000000 : ℝ) (189207685939 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell430_product_lower :
    (672191597395897 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (43 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell430_leftExp
    (by norm_num : (0 : ℝ) ≤ (1711722203 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell430_product_upper :
    Real.pi * Real.exp (431 / 800 : ℝ) ≤ (26921303062998617 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell430_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell430_endpointLower :
    (875451677 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (43 / 160 : ℝ) (431 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (672191597395897 / 125000000000000 : ℝ) (Real.pi * Real.exp (43 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell430_product_lower
  have hD : Real.exp (Real.pi * Real.exp (431 / 800 : ℝ) - (43 / 320 : ℝ)) ≤
      (1905444713269 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell430_denomUpper
    linarith [hpThetaJensenCell430_product_upper]
  have hi : (1 / (1905444713269 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (431 / 800 : ℝ) - (43 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1905444713269 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1905444713269 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((43 / 320 : ℝ) - Real.pi * Real.exp (431 / 800 : ℝ)) := by
    rw [show (43 / 320 : ℝ) - Real.pi * Real.exp (431 / 800 : ℝ) =
      -(Real.pi * Real.exp (431 / 800 : ℝ) - (43 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (43 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (43 / 80 : ℝ)) := by
    have h := hpThetaJensenCell430_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1905444713269 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell430_endpointUpper :
    hpThetaJensenKernelEndpointUpper (43 / 160 : ℝ) (431 / 1600 : ℝ) ≤ (4433001459 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (431 / 800 : ℝ)) (26921303062998617 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (431 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell430_product_upper
  have hD : (189207685939 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (43 / 80 : ℝ) - (431 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell430_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell430_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (43 / 80 : ℝ) - (431 / 3200 : ℝ)) ≤
      (1 / (189207685939 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (189207685939 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((431 / 3200 : ℝ) - Real.pi * Real.exp (43 / 80 : ℝ)) ≤
      (2 / (189207685939 / 1000000000 : ℝ) : ℝ) := by
    rw [show (431 / 3200 : ℝ) - Real.pi * Real.exp (43 / 80 : ℝ) =
      -(Real.pi * Real.exp (43 / 80 : ℝ) - (431 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (26921303062998617 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (26921303062998617 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell430_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (43 / 160 : ℝ) (431 / 1600 : ℝ)) :
    (875451677 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4433001459 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell430_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell430_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell431_leftExp :
    (66947781 / 39062500 : ℝ) ≤ Real.exp (431 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (431 / 800 : ℝ) (1016978460609 / 1000000000000 : ℝ)
    (66947781 / 39062500 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell431_rightExp :
    Real.exp (27 / 50 : ℝ) ≤ (17160068623 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (27 / 50 : ℝ) (1017018187107 / 1000000000000 : ℝ)
    (17160068623 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell431_denomUpper :
    Real.exp (52563076465536439 / 10000000000000000 : ℝ) ≤ (47943023021 / 250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (52563076465536439 / 10000000000000000 : ℝ) (7365751473 /
    6250000000 : ℝ) (47943023021 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell431_denomLower :
    (952125458771 / 5000000000 : ℝ) ≤ Real.exp (25631146963419 / 4882812500000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (25631146963419 / 4882812500000 : ℝ) (589130333811 /
    500000000000 : ℝ) (952125458771 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell431_product_lower :
    (26290326650919 / 4882812500000 : ℝ) ≤ Real.pi * Real.exp (431 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell431_leftExp
    (by norm_num : (0 : ℝ) ≤ (66947781 / 39062500 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell431_product_upper :
    Real.pi * Real.exp (27 / 50 : ℝ) ≤ (53909951465536439 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell431_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell431_endpointLower :
    (8724462587 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (431 / 1600 : ℝ) (27 / 100 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (26290326650919 / 4882812500000 : ℝ) (Real.pi * Real.exp (431 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell431_product_lower
  have hD : Real.exp (Real.pi * Real.exp (27 / 50 : ℝ) - (431 / 3200 : ℝ)) ≤
      (47943023021 / 250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell431_denomUpper
    linarith [hpThetaJensenCell431_product_upper]
  have hi : (1 / (47943023021 / 250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (27 / 50 : ℝ) - (431 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (47943023021 / 250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (47943023021 / 250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((431 / 3200 : ℝ) - Real.pi * Real.exp (27 / 50 : ℝ)) := by
    rw [show (431 / 3200 : ℝ) - Real.pi * Real.exp (27 / 50 : ℝ) =
      -(Real.pi * Real.exp (27 / 50 : ℝ) - (431 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (431 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (431 / 800 : ℝ)) := by
    have h := hpThetaJensenCell431_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (47943023021 / 250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell431_endpointUpper :
    hpThetaJensenKernelEndpointUpper (431 / 1600 : ℝ) (27 / 100 : ℝ) ≤ (8835632963 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (27 / 50 : ℝ)) (53909951465536439 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (27 / 100 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell431_product_upper
  have hD : (952125458771 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (431 / 800 : ℝ) - (27 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell431_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell431_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (431 / 800 : ℝ) - (27 / 200 : ℝ)) ≤
      (1 / (952125458771 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (952125458771 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((27 / 200 : ℝ) - Real.pi * Real.exp (431 / 800 : ℝ)) ≤
      (2 / (952125458771 / 5000000000 : ℝ) : ℝ) := by
    rw [show (27 / 200 : ℝ) - Real.pi * Real.exp (431 / 800 : ℝ) =
      -(Real.pi * Real.exp (431 / 800 : ℝ) - (27 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (53909951465536439 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (53909951465536439 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell431_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (431 / 1600 : ℝ) (27 / 100 : ℝ)) :
    (8724462587 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8835632963 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell431_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell431_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell432_leftExp :
    (17160068621 / 10000000000 : ℝ) ≤ Real.exp (27 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (27 / 50 : ℝ) (508509093553 / 500000000000 : ℝ)
    (17160068621 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell432_rightExp :
    Real.exp (433 / 800 : ℝ) ≤ (429538303 / 250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (433 / 800 : ℝ) (203411583031 / 200000000000 : ℝ)
    (429538303 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell432_denomUpper :
    Real.exp (1315684525936679 / 250000000000000 : ℝ) ≤ (386018495581 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1315684525936679 / 250000000000000 : ℝ) (47150283409 /
    40000000000 : ℝ) (386018495581 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell432_denomLower :
    (383303885943 / 2000000000 : ℝ) ≤ Real.exp (6569601162398079 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6569601162398079 / 1250000000000000 : ℝ) (117849715471 /
    100000000000 : ℝ) (383303885943 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell432_product_lower :
    (6738741787398079 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (27 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell432_leftExp
    (by norm_num : (0 : ℝ) ≤ (17160068621 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell432_product_upper :
    Real.pi * Real.exp (433 / 800 : ℝ) ≤ (1349434525936679 / 250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell432_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell432_endpointLower :
    (271700971 / 312500000 : ℝ) ≤ hpThetaTraceEndpointLower (27 / 100 : ℝ) (433 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6738741787398079 / 1250000000000000 : ℝ) (Real.pi * Real.exp (27 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell432_product_lower
  have hD : Real.exp (Real.pi * Real.exp (433 / 800 : ℝ) - (27 / 200 : ℝ)) ≤
      (386018495581 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell432_denomUpper
    linarith [hpThetaJensenCell432_product_upper]
  have hi : (1 / (386018495581 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (433 / 800 : ℝ) - (27 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (386018495581 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (386018495581 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((27 / 200 : ℝ) - Real.pi * Real.exp (433 / 800 : ℝ)) := by
    rw [show (27 / 200 : ℝ) - Real.pi * Real.exp (433 / 800 : ℝ) =
      -(Real.pi * Real.exp (433 / 800 : ℝ) - (27 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (27 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (27 / 50 : ℝ)) := by
    have h := hpThetaJensenCell432_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (386018495581 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell432_endpointUpper :
    hpThetaJensenKernelEndpointUpper (27 / 100 : ℝ) (433 / 1600 : ℝ) ≤ (2201321403 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (433 / 800 : ℝ)) (1349434525936679 / 250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (433 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell432_product_upper
  have hD : (383303885943 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (27 / 50 : ℝ) - (433 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell432_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell432_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (27 / 50 : ℝ) - (433 / 3200 : ℝ)) ≤
      (1 / (383303885943 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (383303885943 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((433 / 3200 : ℝ) - Real.pi * Real.exp (27 / 50 : ℝ)) ≤
      (2 / (383303885943 / 2000000000 : ℝ) : ℝ) := by
    rw [show (433 / 3200 : ℝ) - Real.pi * Real.exp (27 / 50 : ℝ) =
      -(Real.pi * Real.exp (27 / 50 : ℝ) - (433 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1349434525936679 / 250000000000000 : ℝ) ^ 2 - 6 *
      (1349434525936679 / 250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell432_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (27 / 100 : ℝ) (433 / 1600 : ℝ)) :
    (271700971 / 312500000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2201321403 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell432_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell432_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell433_leftExp :
    (17181532119 / 10000000000 : ℝ) ≤ Real.exp (433 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (433 / 800 : ℝ) (508528957577 / 500000000000 : ℝ)
    (17181532119 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell433_rightExp :
    Real.exp (217 / 400 : ℝ) ≤ (134398613 / 78125000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (217 / 400 : ℝ) (254274411189 / 250000000000 : ℝ)
    (134398613 / 78125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell433_denomUpper :
    Real.exp (411654452748009 / 78125000000000 : ℝ) ≤ (242820028749 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (411654452748009 / 78125000000000 : ℝ) (1178994293117 /
    1000000000000 : ℝ) (242820028749 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell433_denomLower :
    (1928883232219 / 10000000000 : ℝ) ≤ Real.exp (6577639231599181 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6577639231599181 / 1250000000000000 : ℝ) (1178733999549
    / 1000000000000 : ℝ) (1928883232219 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell433_product_lower :
    (6747170481599181 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (433 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell433_leftExp
    (by norm_num : (0 : ℝ) ≤ (17181532119 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell433_product_upper :
    Real.pi * Real.exp (217 / 400 : ℝ) ≤ (422225741810509 / 78125000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell433_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell433_endpointLower :
    (270763207 / 312500000 : ℝ) ≤ hpThetaTraceEndpointLower (433 / 1600 : ℝ) (217 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6747170481599181 / 1250000000000000 : ℝ) (Real.pi * Real.exp (433 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell433_product_lower
  have hD : Real.exp (Real.pi * Real.exp (217 / 400 : ℝ) - (433 / 3200 : ℝ)) ≤
      (242820028749 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell433_denomUpper
    linarith [hpThetaJensenCell433_product_upper]
  have hi : (1 / (242820028749 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (217 / 400 : ℝ) - (433 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (242820028749 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (242820028749 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((433 / 3200 : ℝ) - Real.pi * Real.exp (217 / 400 : ℝ)) := by
    rw [show (433 / 3200 : ℝ) - Real.pi * Real.exp (217 / 400 : ℝ) =
      -(Real.pi * Real.exp (217 / 400 : ℝ) - (433 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (433 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (433 / 800 : ℝ)) := by
    have h := hpThetaJensenCell433_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (242820028749 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell433_endpointUpper :
    hpThetaJensenKernelEndpointUpper (433 / 1600 : ℝ) (217 / 800 : ℝ) ≤ (8774961271 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (217 / 400 : ℝ)) (422225741810509 / 78125000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (217 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell433_product_upper
  have hD : (1928883232219 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (433 / 800 : ℝ) - (217 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell433_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell433_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (433 / 800 : ℝ) - (217 / 1600 : ℝ)) ≤
      (1 / (1928883232219 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1928883232219 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((217 / 1600 : ℝ) - Real.pi * Real.exp (433 / 800 : ℝ)) ≤
      (2 / (1928883232219 / 10000000000 : ℝ) : ℝ) := by
    rw [show (217 / 1600 : ℝ) - Real.pi * Real.exp (433 / 800 : ℝ) =
      -(Real.pi * Real.exp (433 / 800 : ℝ) - (217 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (422225741810509 / 78125000000000 : ℝ) ^ 2 - 6 *
      (422225741810509 / 78125000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell433_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (433 / 1600 : ℝ) (217 / 800 : ℝ)) :
    (270763207 / 312500000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8774961271 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell433_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell433_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell434_leftExp :
    (8601511231 / 5000000000 : ℝ) ≤ Real.exp (217 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (217 / 400 : ℝ) (203419528951 / 200000000000 : ℝ)
    (8601511231 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell434_rightExp :
    Real.exp (87 / 160 : ℝ) ≤ (2153067461 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (87 / 160 : ℝ) (1017137375909 / 1000000000000 : ℝ)
    (2153067461 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell434_denomUpper :
    Real.exp (6594530414005373 / 1250000000000000 : ℝ) ≤ (977562514869 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (6594530414005373 / 1250000000000000 : ℝ) (235846371987 /
    200000000000 : ℝ) (977562514869 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell434_denomLower :
    (194134316817 / 1000000000 : ℝ) ≤ Real.exp (3292843921402469 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3292843921402469 / 625000000000000 : ℝ) (73685700169 /
    62500000000 : ℝ) (194134316817 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell434_product_lower :
    (3377804858902469 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (217 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell434_leftExp
    (by norm_num : (0 : ℝ) ≤ (8601511231 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell434_product_upper :
    Real.pi * Real.exp (87 / 160 : ℝ) ≤ (6764061664005373 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell434_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell434_endpointLower :
    (4317218821 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (217 / 800 : ℝ) (87 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3377804858902469 / 625000000000000 : ℝ) (Real.pi * Real.exp (217 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell434_product_lower
  have hD : Real.exp (Real.pi * Real.exp (87 / 160 : ℝ) - (217 / 1600 : ℝ)) ≤
      (977562514869 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell434_denomUpper
    linarith [hpThetaJensenCell434_product_upper]
  have hi : (1 / (977562514869 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (87 / 160 : ℝ) - (217 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (977562514869 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (977562514869 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((217 / 1600 : ℝ) - Real.pi * Real.exp (87 / 160 : ℝ)) := by
    rw [show (217 / 1600 : ℝ) - Real.pi * Real.exp (87 / 160 : ℝ) =
      -(Real.pi * Real.exp (87 / 160 : ℝ) - (217 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (217 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (217 / 400 : ℝ)) := by
    have h := hpThetaJensenCell434_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (977562514869 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell434_endpointUpper :
    hpThetaJensenKernelEndpointUpper (217 / 800 : ℝ) (87 / 320 : ℝ) ≤ (2186165087 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (87 / 160 : ℝ)) (6764061664005373 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (87 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell434_product_upper
  have hD : (194134316817 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (217 / 400 : ℝ) - (87 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell434_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell434_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (217 / 400 : ℝ) - (87 / 640 : ℝ)) ≤
      (1 / (194134316817 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (194134316817 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((87 / 640 : ℝ) - Real.pi * Real.exp (217 / 400 : ℝ)) ≤
      (2 / (194134316817 / 1000000000 : ℝ) : ℝ) := by
    rw [show (87 / 640 : ℝ) - Real.pi * Real.exp (217 / 400 : ℝ) =
      -(Real.pi * Real.exp (217 / 400 : ℝ) - (87 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (6764061664005373 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (6764061664005373 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell434_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (217 / 800 : ℝ) (87 / 320 : ℝ)) :
    (4317218821 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2186165087 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell434_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell434_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell435_leftExp :
    (8612269843 / 5000000000 : ℝ) ≤ Real.exp (87 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (87 / 160 : ℝ) (254284343977 / 250000000000 : ℝ)
    (8612269843 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell435_rightExp :
    Real.exp (109 / 200 : ℝ) ≤ (689843353 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (109 / 200 : ℝ) (508588554307 / 500000000000 : ℝ)
    (689843353 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell435_denomUpper :
    Real.exp (2112832048881329 / 400000000000000 : ℝ) ≤ (122986733639 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (2112832048881329 / 400000000000000 : ℝ) (58973489313 /
    50000000000 : ℝ) (122986733639 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell435_denomLower :
    (1953900091609 / 10000000000 : ℝ) ≤ Real.exp (3296873505076257 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3296873505076257 / 625000000000000 : ℝ) (1179208764791 /
    1000000000000 : ℝ) (1953900091609 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell435_product_lower :
    (3382029755076257 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (87 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell435_leftExp
    (by norm_num : (0 : ℝ) ≤ (8612269843 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell435_product_upper :
    Real.pi * Real.exp (109 / 200 : ℝ) ≤ (2167207048881329 / 400000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell435_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell435_endpointLower :
    (860447653 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (87 / 320 : ℝ) (109 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3382029755076257 / 625000000000000 : ℝ) (Real.pi * Real.exp (87 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell435_product_lower
  have hD : Real.exp (Real.pi * Real.exp (109 / 200 : ℝ) - (87 / 640 : ℝ)) ≤
      (122986733639 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell435_denomUpper
    linarith [hpThetaJensenCell435_product_upper]
  have hi : (1 / (122986733639 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (109 / 200 : ℝ) - (87 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (122986733639 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (122986733639 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((87 / 640 : ℝ) - Real.pi * Real.exp (109 / 200 : ℝ)) := by
    rw [show (87 / 640 : ℝ) - Real.pi * Real.exp (109 / 200 : ℝ) =
      -(Real.pi * Real.exp (109 / 200 : ℝ) - (87 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (87 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (87 / 160 : ℝ)) := by
    have h := hpThetaJensenCell435_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (122986733639 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell435_endpointUpper :
    hpThetaJensenKernelEndpointUpper (87 / 320 : ℝ) (109 / 400 : ℝ) ≤ (217859581 / 250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (109 / 200 : ℝ)) (2167207048881329 / 400000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (109 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell435_product_upper
  have hD : (1953900091609 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (87 / 160 : ℝ) - (109 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell435_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell435_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (87 / 160 : ℝ) - (109 / 800 : ℝ)) ≤
      (1 / (1953900091609 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1953900091609 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((109 / 800 : ℝ) - Real.pi * Real.exp (87 / 160 : ℝ)) ≤
      (2 / (1953900091609 / 10000000000 : ℝ) : ℝ) := by
    rw [show (109 / 800 : ℝ) - Real.pi * Real.exp (87 / 160 : ℝ) =
      -(Real.pi * Real.exp (87 / 160 : ℝ) - (109 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2167207048881329 / 400000000000000 : ℝ) ^ 2 - 6 *
      (2167207048881329 / 400000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell435_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (87 / 320 : ℝ) (109 / 400 : ℝ)) :
    (860447653 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (217859581 / 250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell435_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell435_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell436_leftExp :
    (17246083823 / 10000000000 : ℝ) ≤ Real.exp (109 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (109 / 200 : ℝ) (1017177108613 / 1000000000000 : ℝ)
    (17246083823 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell436_rightExp :
    Real.exp (437 / 800 : ℝ) ≤ (17267654909 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (437 / 800 : ℝ) (1017216842871 / 1000000000000 : ℝ)
    (17267654909 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell436_denomUpper :
    Real.exp (52885443788530037 / 10000000000000000 : ℝ) ≤ (1980549225543 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (52885443788530037 / 10000000000000000 : ℝ) (294927018171
    / 250000000000 : ℝ) (1980549225543 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell436_denomLower :
    (983277431171 / 5000000000 : ℝ) ≤ Real.exp (6601816746208277 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6601816746208277 / 1250000000000000 : ℝ) (1179446686377
    / 1000000000000 : ℝ) (983277431171 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell436_product_lower :
    (6772519871208277 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (109 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell436_leftExp
    (by norm_num : (0 : ℝ) ≤ (17246083823 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell436_product_upper :
    Real.pi * Real.exp (437 / 800 : ℝ) ≤ (54247943788530037 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell436_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell436_endpointLower :
    (2143634921 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (109 / 400 : ℝ) (437 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6772519871208277 / 1250000000000000 : ℝ) (Real.pi * Real.exp (109 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell436_product_lower
  have hD : Real.exp (Real.pi * Real.exp (437 / 800 : ℝ) - (109 / 800 : ℝ)) ≤
      (1980549225543 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell436_denomUpper
    linarith [hpThetaJensenCell436_product_upper]
  have hi : (1 / (1980549225543 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (437 / 800 : ℝ) - (109 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1980549225543 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1980549225543 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((109 / 800 : ℝ) - Real.pi * Real.exp (437 / 800 : ℝ)) := by
    rw [show (109 / 800 : ℝ) - Real.pi * Real.exp (437 / 800 : ℝ) =
      -(Real.pi * Real.exp (437 / 800 : ℝ) - (109 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (109 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (109 / 200 : ℝ)) := by
    have h := hpThetaJensenCell436_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1980549225543 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell436_endpointUpper :
    hpThetaJensenKernelEndpointUpper (109 / 400 : ℝ) (437 / 1600 : ℝ) ≤ (4342065177 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (437 / 800 : ℝ)) (54247943788530037 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (437 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell436_product_upper
  have hD : (983277431171 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (109 / 200 : ℝ) - (437 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell436_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell436_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (109 / 200 : ℝ) - (437 / 3200 : ℝ)) ≤
      (1 / (983277431171 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (983277431171 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((437 / 3200 : ℝ) - Real.pi * Real.exp (109 / 200 : ℝ)) ≤
      (2 / (983277431171 / 5000000000 : ℝ) : ℝ) := by
    rw [show (437 / 3200 : ℝ) - Real.pi * Real.exp (109 / 200 : ℝ) =
      -(Real.pi * Real.exp (109 / 200 : ℝ) - (437 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (54247943788530037 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (54247943788530037 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell436_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (109 / 400 : ℝ) (437 / 1600 : ℝ)) :
    (2143634921 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4342065177 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell436_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell436_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell437_leftExp :
    (17267654907 / 10000000000 : ℝ) ≤ Real.exp (437 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (437 / 800 : ℝ) (101721684287 / 100000000000 : ℝ)
    (17267654907 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell437_rightExp :
    Real.exp (219 / 400 : ℝ) ≤ (17289252973 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (219 / 400 : ℝ) (25431414467 / 25000000000 : ℝ)
    (17289252973 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell437_denomUpper :
    Real.exp (52950171115205989 / 10000000000000000 : ℝ) ≤ (1993410369673 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (52950171115205989 / 10000000000000000 : ℝ)
    (1179946719787 / 1000000000000 : ℝ) (1993410369673 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell437_denomLower :
    (494827087479 / 2500000000 : ℝ) ≤ Real.exp (6609897064323993 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6609897064323993 / 1250000000000000 : ℝ) (589842484027 /
    500000000000 : ℝ) (494827087479 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell437_product_lower :
    (6780990814323993 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (437 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell437_leftExp
    (by norm_num : (0 : ℝ) ≤ (17267654907 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell437_product_upper :
    Real.pi * Real.exp (219 / 400 : ℝ) ≤ (54315796115205989 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell437_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell437_endpointLower :
    (8544627501 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (437 / 1600 : ℝ) (219 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6780990814323993 / 1250000000000000 : ℝ) (Real.pi * Real.exp (437 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell437_product_lower
  have hD : Real.exp (Real.pi * Real.exp (219 / 400 : ℝ) - (437 / 3200 : ℝ)) ≤
      (1993410369673 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell437_denomUpper
    linarith [hpThetaJensenCell437_product_upper]
  have hi : (1 / (1993410369673 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (219 / 400 : ℝ) - (437 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1993410369673 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1993410369673 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((437 / 3200 : ℝ) - Real.pi * Real.exp (219 / 400 : ℝ)) := by
    rw [show (437 / 3200 : ℝ) - Real.pi * Real.exp (219 / 400 : ℝ) =
      -(Real.pi * Real.exp (219 / 400 : ℝ) - (437 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (437 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (437 / 800 : ℝ)) := by
    have h := hpThetaJensenCell437_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1993410369673 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell437_endpointUpper :
    hpThetaJensenKernelEndpointUpper (437 / 1600 : ℝ) (219 / 800 : ℝ) ≤ (8653902089 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (219 / 400 : ℝ)) (54315796115205989 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (219 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell437_product_upper
  have hD : (494827087479 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (437 / 800 : ℝ) - (219 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell437_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell437_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (437 / 800 : ℝ) - (219 / 1600 : ℝ)) ≤
      (1 / (494827087479 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (494827087479 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((219 / 1600 : ℝ) - Real.pi * Real.exp (437 / 800 : ℝ)) ≤
      (2 / (494827087479 / 2500000000 : ℝ) : ℝ) := by
    rw [show (219 / 1600 : ℝ) - Real.pi * Real.exp (437 / 800 : ℝ) =
      -(Real.pi * Real.exp (437 / 800 : ℝ) - (219 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (54315796115205989 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (54315796115205989 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell437_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (437 / 1600 : ℝ) (219 / 800 : ℝ)) :
    (8544627501 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8653902089 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell437_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell437_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell438_leftExp :
    (4322313243 / 2500000000 : ℝ) ≤ Real.exp (219 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (219 / 400 : ℝ) (1017256578679 / 1000000000000 : ℝ)
    (4322313243 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell438_rightExp :
    Real.exp (439 / 800 : ℝ) ≤ (4327719513 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (439 / 800 : ℝ) (1017296316041 / 1000000000000 : ℝ)
    (4327719513 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell438_denomUpper :
    Real.exp (13253745828004209 / 2500000000000000 : ℝ) ≤ (2006372058609 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (13253745828004209 / 2500000000000000 : ℝ) (47207429127 /
    40000000000 : ℝ) (2006372058609 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell438_denomLower :
    (1992161432461 / 10000000000 : ℝ) ≤ Real.exp (1654496994462857 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1654496994462857 / 312500000000000 : ℝ) (235984722083 /
    200000000000 : ℝ) (1992161432461 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell438_product_lower :
    (1697368088212857 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (219 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell438_leftExp
    (by norm_num : (0 : ℝ) ≤ (4322313243 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell438_product_upper :
    Real.pi * Real.exp (439 / 800 : ℝ) ≤ (13595933328004209 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell438_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell438_endpointLower :
    (4257370187 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (219 / 800 : ℝ) (439 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1697368088212857 / 312500000000000 : ℝ) (Real.pi * Real.exp (219 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell438_product_lower
  have hD : Real.exp (Real.pi * Real.exp (439 / 800 : ℝ) - (219 / 1600 : ℝ)) ≤
      (2006372058609 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell438_denomUpper
    linarith [hpThetaJensenCell438_product_upper]
  have hi : (1 / (2006372058609 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (439 / 800 : ℝ) - (219 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2006372058609 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2006372058609 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((219 / 1600 : ℝ) - Real.pi * Real.exp (439 / 800 : ℝ)) := by
    rw [show (219 / 1600 : ℝ) - Real.pi * Real.exp (439 / 800 : ℝ) =
      -(Real.pi * Real.exp (439 / 800 : ℝ) - (219 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (219 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (219 / 400 : ℝ)) := by
    have h := hpThetaJensenCell438_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2006372058609 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell438_endpointUpper :
    hpThetaJensenKernelEndpointUpper (219 / 800 : ℝ) (439 / 1600 : ℝ) ≤ (1724739769 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (439 / 800 : ℝ)) (13595933328004209 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (439 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell438_product_upper
  have hD : (1992161432461 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (219 / 400 : ℝ) - (439 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell438_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell438_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (219 / 400 : ℝ) - (439 / 3200 : ℝ)) ≤
      (1 / (1992161432461 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1992161432461 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((439 / 3200 : ℝ) - Real.pi * Real.exp (219 / 400 : ℝ)) ≤
      (2 / (1992161432461 / 10000000000 : ℝ) : ℝ) := by
    rw [show (439 / 3200 : ℝ) - Real.pi * Real.exp (219 / 400 : ℝ) =
      -(Real.pi * Real.exp (219 / 400 : ℝ) - (439 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (13595933328004209 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (13595933328004209 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell438_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (219 / 800 : ℝ) (439 / 1600 : ℝ)) :
    (4257370187 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1724739769 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell438_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell438_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell439_leftExp :
    (17310878051 / 10000000000 : ℝ) ≤ Real.exp (439 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (439 / 800 : ℝ) (25432407901 / 25000000000 : ℝ)
    (17310878051 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell439_rightExp :
    Real.exp (11 / 20 : ℝ) ≤ (17332530179 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11 / 20 : ℝ) (508668027477 / 500000000000 : ℝ)
    (17332530179 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell439_denomUpper :
    Real.exp (53079880482635147 / 10000000000000000 : ℝ) ≤ (2019435187761 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (53079880482635147 / 10000000000000000 : ℝ) (118042509843
    / 100000000000 : ℝ) (2019435187761 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell439_denomLower :
    (1002557498061 / 5000000000 : ℝ) ≤ Real.exp (6626089499749649 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6626089499749649 / 1250000000000000 : ℝ) (590081307021 /
    500000000000 : ℝ) (1002557498061 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell439_product_lower :
    (6797964499749649 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (439 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell439_leftExp
    (by norm_num : (0 : ℝ) ≤ (17310878051 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell439_product_upper :
    Real.pi * Real.exp (11 / 20 : ℝ) ≤ (54451755482635147 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell439_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell439_endpointLower :
    (8484878697 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (439 / 1600 : ℝ) (11 / 40 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6797964499749649 / 1250000000000000 : ℝ) (Real.pi * Real.exp (439 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell439_product_lower
  have hD : Real.exp (Real.pi * Real.exp (11 / 20 : ℝ) - (439 / 3200 : ℝ)) ≤
      (2019435187761 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell439_denomUpper
    linarith [hpThetaJensenCell439_product_upper]
  have hi : (1 / (2019435187761 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (11 / 20 : ℝ) - (439 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2019435187761 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2019435187761 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((439 / 3200 : ℝ) - Real.pi * Real.exp (11 / 20 : ℝ)) := by
    rw [show (439 / 3200 : ℝ) - Real.pi * Real.exp (11 / 20 : ℝ) =
      -(Real.pi * Real.exp (11 / 20 : ℝ) - (439 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (439 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (439 / 800 : ℝ)) := by
    have h := hpThetaJensenCell439_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2019435187761 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell439_endpointUpper :
    hpThetaJensenKernelEndpointUpper (439 / 1600 : ℝ) (11 / 40 : ℝ) ≤ (4296760511 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (11 / 20 : ℝ)) (54451755482635147 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (11 / 40 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell439_product_upper
  have hD : (1002557498061 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (439 / 800 : ℝ) - (11 / 80 : ℝ)) := by
    apply le_trans hpThetaJensenCell439_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell439_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (439 / 800 : ℝ) - (11 / 80 : ℝ)) ≤
      (1 / (1002557498061 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1002557498061 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((11 / 80 : ℝ) - Real.pi * Real.exp (439 / 800 : ℝ)) ≤
      (2 / (1002557498061 / 5000000000 : ℝ) : ℝ) := by
    rw [show (11 / 80 : ℝ) - Real.pi * Real.exp (439 / 800 : ℝ) =
      -(Real.pi * Real.exp (439 / 800 : ℝ) - (11 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (54451755482635147 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (54451755482635147 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell439_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (439 / 1600 : ℝ) (11 / 40 : ℝ)) :
    (8484878697 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4296760511 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell439_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell439_endpointUpper

def hpThetaJensenCellsBatch021Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (9056215833 / 10000000000 : ℝ)
  | 1 => (45129787 / 50000000 : ℝ)
  | 2 => (2248929383 / 2500000000 : ℝ)
  | 3 => (1793099331 / 2000000000 : ℝ)
  | 4 => (8935295179 / 10000000000 : ℝ)
  | 5 => (1781022703 / 2000000000 : ℝ)
  | 6 => (8874952079 / 10000000000 : ℝ)
  | 7 => (8844811279 / 10000000000 : ℝ)
  | 8 => (8814691523 / 10000000000 : ℝ)
  | 9 => (8784593219 / 10000000000 : ℝ)
  | 10 => (875451677 / 1000000000 : ℝ)
  | 11 => (8724462587 / 10000000000 : ℝ)
  | 12 => (271700971 / 312500000 : ℝ)
  | 13 => (270763207 / 312500000 : ℝ)
  | 14 => (4317218821 / 5000000000 : ℝ)
  | 15 => (860447653 / 1000000000 : ℝ)
  | 16 => (2143634921 / 2500000000 : ℝ)
  | 17 => (8544627501 / 10000000000 : ℝ)
  | 18 => (4257370187 / 5000000000 : ℝ)
  | 19 => (8484878697 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch021Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1146356903 / 1250000000 : ℝ)
  | 1 => (1828056379 / 2000000000 : ℝ)
  | 2 => (4554863517 / 5000000000 : ℝ)
  | 3 => (2269797763 / 2500000000 : ℝ)
  | 4 => (4524337187 / 5000000000 : ℝ)
  | 5 => (9018177413 / 10000000000 : ℝ)
  | 6 => (8987700589 / 10000000000 : ℝ)
  | 7 => (1119655539 / 1250000000 : ℝ)
  | 8 => (8926809001 / 10000000000 : ℝ)
  | 9 => (1779279013 / 2000000000 : ℝ)
  | 10 => (4433001459 / 5000000000 : ℝ)
  | 11 => (8835632963 / 10000000000 : ℝ)
  | 12 => (2201321403 / 2500000000 : ℝ)
  | 13 => (8774961271 / 10000000000 : ℝ)
  | 14 => (2186165087 / 2500000000 : ℝ)
  | 15 => (217859581 / 250000000 : ℝ)
  | 16 => (4342065177 / 5000000000 : ℝ)
  | 17 => (8653902089 / 10000000000 : ℝ)
  | 18 => (1724739769 / 2000000000 : ℝ)
  | 19 => (4296760511 / 5000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch021_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((420 : ℝ) + (j.val : ℝ)) / 1600)
      (((420 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch021Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch021Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell420_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell421_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell422_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell423_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell424_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell425_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell426_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell427_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell428_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell429_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell430_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell431_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell432_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell433_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell434_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell435_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell436_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell437_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell438_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell439_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper] at h ⊢
    exact h

end HodgeProofHP
