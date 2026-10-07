import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell300_leftExp :
    (7274957073 / 5000000000 : ℝ) ≤ Real.exp (3 / 8 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3 / 8 : ℝ) (1011787683559 / 1000000000000 : ℝ)
    (7274957073 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell300_rightExp :
    Real.exp (301 / 800 : ℝ) ≤ (14568112911 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (301 / 800 : ℝ) (126478400911 / 125000000000 : ℝ)
    (14568112911 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell300_denomUpper :
    Real.exp (44829581544407223 / 10000000000000000 : ℝ) ≤ (884960709043 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (44829581544407223 / 10000000000000000 : ℝ)
    (1150380137759 / 1000000000000 : ℝ) (884960709043 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell300_denomLower :
    (879639338757 / 10000000000 : ℝ) ≤ Real.exp (2798079305110027 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2798079305110027 / 625000000000000 : ℝ) (115016333791 /
    100000000000 : ℝ) (879639338757 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell300_product_lower :
    (2856868367610027 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (3 / 8 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell300_leftExp
    (by norm_num : (0 : ℝ) ≤ (7274957073 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell300_product_upper :
    Real.pi * Real.exp (301 / 800 : ℝ) ≤ (45767081544407223 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell300_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell300_endpointLower :
    (507591707 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (3 / 16 : ℝ) (301 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2856868367610027 / 625000000000000 : ℝ) (Real.pi * Real.exp (3 / 8 : ℝ))
    (by norm_num) hpThetaJensenCell300_product_lower
  have hD : Real.exp (Real.pi * Real.exp (301 / 800 : ℝ) - (3 / 32 : ℝ)) ≤
      (884960709043 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell300_denomUpper
    linarith [hpThetaJensenCell300_product_upper]
  have hi : (1 / (884960709043 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (301 / 800 : ℝ) - (3 / 32 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (884960709043 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (884960709043 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((3 / 32 : ℝ) - Real.pi * Real.exp (301 / 800 : ℝ)) := by
    rw [show (3 / 32 : ℝ) - Real.pi * Real.exp (301 / 800 : ℝ) =
      -(Real.pi * Real.exp (301 / 800 : ℝ) - (3 / 32 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (3 / 8 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (3 / 8 : ℝ)) := by
    have h := hpThetaJensenCell300_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (884960709043 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell300_endpointUpper :
    hpThetaJensenKernelEndpointUpper (3 / 16 : ℝ) (301 / 1600 : ℝ) ≤ (6420030529 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (301 / 800 : ℝ)) (45767081544407223 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (301 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell300_product_upper
  have hD : (879639338757 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (3 / 8 : ℝ) - (301 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell300_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell300_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (3 / 8 : ℝ) - (301 / 3200 : ℝ)) ≤
      (1 / (879639338757 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (879639338757 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((301 / 3200 : ℝ) - Real.pi * Real.exp (3 / 8 : ℝ)) ≤
      (2 / (879639338757 / 10000000000 : ℝ) : ℝ) := by
    rw [show (301 / 3200 : ℝ) - Real.pi * Real.exp (3 / 8 : ℝ) =
      -(Real.pi * Real.exp (3 / 8 : ℝ) - (301 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (45767081544407223 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (45767081544407223 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell300_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (3 / 16 : ℝ) (301 / 1600 : ℝ)) :
    (507591707 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6420030529 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell300_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell300_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell301_leftExp :
    (1456811291 / 1000000000 : ℝ) ≤ Real.exp (301 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (301 / 800 : ℝ) (1011827207287 / 1000000000000 : ℝ)
    (1456811291 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell301_rightExp :
    Real.exp (151 / 400 : ℝ) ≤ (7293167219 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (151 / 400 : ℝ) (12648334157 / 12500000000 : ℝ)
    (7293167219 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell301_denomUpper :
    Real.exp (22441850583039867 / 5000000000000000 : ℝ) ≤ (222440766567 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (22441850583039867 / 5000000000000000 : ℝ) (287643677723
    / 250000000000 : ℝ) (222440766567 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell301_denomLower :
    (35376259707 / 400000000 : ℝ) ≤ Real.exp (560291462164409 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (560291462164409 / 125000000000000 : ℝ) (1150357617233 /
    1000000000000 : ℝ) (35376259707 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell301_product_lower :
    (572088337164409 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (301 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell301_leftExp
    (by norm_num : (0 : ℝ) ≤ (1456811291 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell301_product_upper :
    Real.pi * Real.exp (151 / 400 : ℝ) ≤ (22912163083039867 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell301_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell301_endpointLower :
    (24727763 / 19531250 : ℝ) ≤ hpThetaTraceEndpointLower (301 / 1600 : ℝ) (151 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (572088337164409 / 125000000000000 : ℝ) (Real.pi * Real.exp (301 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell301_product_lower
  have hD : Real.exp (Real.pi * Real.exp (151 / 400 : ℝ) - (301 / 3200 : ℝ)) ≤
      (222440766567 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell301_denomUpper
    linarith [hpThetaJensenCell301_product_upper]
  have hi : (1 / (222440766567 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (151 / 400 : ℝ) - (301 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (222440766567 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (222440766567 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((301 / 3200 : ℝ) - Real.pi * Real.exp (151 / 400 : ℝ)) := by
    rw [show (301 / 3200 : ℝ) - Real.pi * Real.exp (151 / 400 : ℝ) =
      -(Real.pi * Real.exp (151 / 400 : ℝ) - (301 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (301 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (301 / 800 : ℝ)) := by
    have h := hpThetaJensenCell301_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (222440766567 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell301_endpointUpper :
    hpThetaJensenKernelEndpointUpper (301 / 1600 : ℝ) (151 / 800 : ℝ) ≤ (12810614637 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (151 / 400 : ℝ)) (22912163083039867 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (151 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell301_product_upper
  have hD : (35376259707 / 400000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (301 / 800 : ℝ) - (151 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell301_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell301_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (301 / 800 : ℝ) - (151 / 1600 : ℝ)) ≤
      (1 / (35376259707 / 400000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (35376259707 / 400000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((151 / 1600 : ℝ) - Real.pi * Real.exp (301 / 800 : ℝ)) ≤
      (2 / (35376259707 / 400000000 : ℝ) : ℝ) := by
    rw [show (151 / 1600 : ℝ) - Real.pi * Real.exp (301 / 800 : ℝ) =
      -(Real.pi * Real.exp (301 / 800 : ℝ) - (151 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (22912163083039867 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (22912163083039867 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell301_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (301 / 1600 : ℝ) (151 / 800 : ℝ)) :
    (24727763 / 19531250 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (12810614637 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell301_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell301_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell302_leftExp :
    (14586334437 / 10000000000 : ℝ) ≤ Real.exp (151 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (151 / 400 : ℝ) (1011866732559 / 1000000000000 : ℝ)
    (14586334437 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell302_rightExp :
    Real.exp (303 / 800 : ℝ) ≤ (14604578757 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (303 / 800 : ℝ) (1011906259377 / 1000000000000 : ℝ)
    (14604578757 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell302_denomUpper :
    Real.exp (44937892390939901 / 10000000000000000 : ℝ) ≤ (111824736217 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (44937892390939901 / 10000000000000000 : ℝ) (35961549201
    / 31250000000 : ℝ) (111824736217 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell302_denomLower :
    (177841168153 / 2000000000 : ℝ) ≤ Real.exp (5609679572075463 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5609679572075463 / 1250000000000000 : ℝ) (287638046623 /
    250000000000 : ℝ) (177841168153 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell302_product_lower :
    (5728038947075463 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (151 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell302_leftExp
    (by norm_num : (0 : ℝ) ≤ (14586334437 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell302_product_upper :
    Real.pi * Real.exp (303 / 800 : ℝ) ≤ (45881642390939901 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell302_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell302_endpointLower :
    (12631398969 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (151 / 800 : ℝ) (303 / 1600 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5728038947075463 / 1250000000000000 : ℝ) (Real.pi * Real.exp (151 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell302_product_lower
  have hD : Real.exp (Real.pi * Real.exp (303 / 800 : ℝ) - (151 / 1600 : ℝ)) ≤
      (111824736217 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell302_denomUpper
    linarith [hpThetaJensenCell302_product_upper]
  have hi : (1 / (111824736217 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (303 / 800 : ℝ) - (151 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (111824736217 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (111824736217 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((151 / 1600 : ℝ) - Real.pi * Real.exp (303 / 800 : ℝ)) := by
    rw [show (151 / 1600 : ℝ) - Real.pi * Real.exp (303 / 800 : ℝ) =
      -(Real.pi * Real.exp (303 / 800 : ℝ) - (151 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (151 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (151 / 400 : ℝ)) := by
    have h := hpThetaJensenCell302_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (111824736217 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell302_endpointUpper :
    hpThetaJensenKernelEndpointUpper (151 / 800 : ℝ) (303 / 1600 : ℝ) ≤ (12781129901 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (303 / 800 : ℝ)) (45881642390939901 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (303 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell302_product_upper
  have hD : (177841168153 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (151 / 400 : ℝ) - (303 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell302_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell302_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (151 / 400 : ℝ) - (303 / 3200 : ℝ)) ≤
      (1 / (177841168153 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (177841168153 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((303 / 3200 : ℝ) - Real.pi * Real.exp (151 / 400 : ℝ)) ≤
      (2 / (177841168153 / 2000000000 : ℝ) : ℝ) := by
    rw [show (303 / 3200 : ℝ) - Real.pi * Real.exp (151 / 400 : ℝ) =
      -(Real.pi * Real.exp (151 / 400 : ℝ) - (303 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (45881642390939901 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (45881642390939901 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell302_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (151 / 800 : ℝ) (303 / 1600 : ℝ)) :
    (12631398969 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (12781129901 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell302_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell302_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell303_leftExp :
    (3651144689 / 2500000000 : ℝ) ≤ Real.exp (303 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (303 / 800 : ℝ) (63244141211 / 62500000000 : ℝ)
    (3651144689 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell303_rightExp :
    Real.exp (19 / 50 : ℝ) ≤ (2924569179 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (19 / 50 : ℝ) (1011945787737 / 1000000000000 : ℝ)
    (2924569179 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell303_denomUpper :
    Real.exp (8998431060762147 / 2000000000000000 : ℝ) ≤ (899465432881 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8998431060762147 / 2000000000000000 : ℝ) (1150964728819
    / 1000000000000 : ℝ) (899465432881 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell303_denomLower :
    (894037634741 / 10000000000 : ℝ) ≤ Real.exp (1404113368225611 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1404113368225611 / 312500000000000 : ℝ) (143843380769 /
    125000000000 : ℝ) (894037634741 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell303_product_lower :
    (1433800868225611 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (303 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell303_leftExp
    (by norm_num : (0 : ℝ) ≤ (3651144689 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell303_product_upper :
    Real.pi * Real.exp (19 / 50 : ℝ) ≤ (9187806060762147 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell303_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell303_endpointLower :
    (6301073057 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (303 / 1600 : ℝ) (19 / 100 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1433800868225611 / 312500000000000 : ℝ) (Real.pi * Real.exp (303 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell303_product_lower
  have hD : Real.exp (Real.pi * Real.exp (19 / 50 : ℝ) - (303 / 3200 : ℝ)) ≤
      (899465432881 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell303_denomUpper
    linarith [hpThetaJensenCell303_product_upper]
  have hi : (1 / (899465432881 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (19 / 50 : ℝ) - (303 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (899465432881 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (899465432881 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((303 / 3200 : ℝ) - Real.pi * Real.exp (19 / 50 : ℝ)) := by
    rw [show (303 / 3200 : ℝ) - Real.pi * Real.exp (19 / 50 : ℝ) =
      -(Real.pi * Real.exp (19 / 50 : ℝ) - (303 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (303 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (303 / 800 : ℝ)) := by
    have h := hpThetaJensenCell303_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (899465432881 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell303_endpointUpper :
    hpThetaJensenKernelEndpointUpper (303 / 1600 : ℝ) (19 / 100 : ℝ) ≤ (12751607339 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (19 / 50 : ℝ)) (9187806060762147 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (19 / 100 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell303_product_upper
  have hD : (894037634741 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (303 / 800 : ℝ) - (19 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell303_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell303_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (303 / 800 : ℝ) - (19 / 200 : ℝ)) ≤
      (1 / (894037634741 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (894037634741 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((19 / 200 : ℝ) - Real.pi * Real.exp (303 / 800 : ℝ)) ≤
      (2 / (894037634741 / 10000000000 : ℝ) : ℝ) := by
    rw [show (19 / 200 : ℝ) - Real.pi * Real.exp (303 / 800 : ℝ) =
      -(Real.pi * Real.exp (303 / 800 : ℝ) - (19 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9187806060762147 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (9187806060762147 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell303_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (303 / 1600 : ℝ) (19 / 100 : ℝ)) :
    (6301073057 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (12751607339 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell303_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell303_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell304_leftExp :
    (7311422947 / 5000000000 : ℝ) ≤ Real.exp (19 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (19 / 50 : ℝ) (126493223467 / 125000000000 : ℝ)
    (7311422947 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell304_rightExp :
    Real.exp (61 / 160 : ℝ) ≤ (14641135881 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (61 / 160 : ℝ) (1011985317641 / 1000000000000 : ℝ)
    (14641135881 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell304_denomUpper :
    Real.exp (45046489995798433 / 10000000000000000 : ℝ) ≤ (226091487991 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (45046489995798433 / 10000000000000000 : ℝ) (575580087259
    / 500000000000 : ℝ) (226091487991 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell304_denomLower :
    (449451063927 / 5000000000 : ℝ) ≤ Real.exp (2811618167363953 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2811618167363953 / 625000000000000 : ℝ) (287735549163 /
    250000000000 : ℝ) (449451063927 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell304_product_lower :
    (2871188479863953 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (19 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell304_leftExp
    (by norm_num : (0 : ℝ) ≤ (7311422947 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell304_product_upper :
    Real.pi * Real.exp (61 / 160 : ℝ) ≤ (45996489995798433 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell304_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell304_endpointLower :
    (628642829 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (19 / 100 : ℝ) (61 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2871188479863953 / 625000000000000 : ℝ) (Real.pi * Real.exp (19 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell304_product_lower
  have hD : Real.exp (Real.pi * Real.exp (61 / 160 : ℝ) - (19 / 200 : ℝ)) ≤
      (226091487991 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell304_denomUpper
    linarith [hpThetaJensenCell304_product_upper]
  have hi : (1 / (226091487991 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (61 / 160 : ℝ) - (19 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (226091487991 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (226091487991 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((19 / 200 : ℝ) - Real.pi * Real.exp (61 / 160 : ℝ)) := by
    rw [show (19 / 200 : ℝ) - Real.pi * Real.exp (61 / 160 : ℝ) =
      -(Real.pi * Real.exp (61 / 160 : ℝ) - (19 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (19 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (19 / 50 : ℝ)) := by
    have h := hpThetaJensenCell304_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (226091487991 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell304_endpointUpper :
    hpThetaJensenKernelEndpointUpper (19 / 100 : ℝ) (61 / 320 : ℝ) ≤ (12722047459 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (61 / 160 : ℝ)) (45996489995798433 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (61 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell304_product_upper
  have hD : (449451063927 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (19 / 50 : ℝ) - (61 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell304_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell304_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (19 / 50 : ℝ) - (61 / 640 : ℝ)) ≤
      (1 / (449451063927 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (449451063927 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((61 / 640 : ℝ) - Real.pi * Real.exp (19 / 50 : ℝ)) ≤
      (2 / (449451063927 / 5000000000 : ℝ) : ℝ) := by
    rw [show (61 / 640 : ℝ) - Real.pi * Real.exp (19 / 50 : ℝ) =
      -(Real.pi * Real.exp (19 / 50 : ℝ) - (61 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (45996489995798433 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (45996489995798433 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell304_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (19 / 100 : ℝ) (61 / 320 : ℝ)) :
    (628642829 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (12722047459 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell304_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell304_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell305_leftExp :
    (366028397 / 250000000 : ℝ) ≤ Real.exp (61 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (61 / 160 : ℝ) (25299632941 / 25000000000 : ℝ) (366028397
    / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell305_rightExp :
    Real.exp (153 / 400 : ℝ) ≤ (1832431093 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (153 / 400 : ℝ) (101202484909 / 100000000000 : ℝ)
    (1832431093 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell305_denomUpper :
    Real.exp (5637612069751149 / 1250000000000000 : ℝ) ≤ (909299705449 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (5637612069751149 / 1250000000000000 : ℝ) (1151355911993
    / 1000000000000 : ℝ) (909299705449 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell305_denomLower :
    (903799576253 / 10000000000 : ℝ) ≤ Real.exp (140750704223503 / 31250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (140750704223503 / 31250000000000 : ℝ) (1151137638459 /
    1000000000000 : ℝ) (903799576253 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell305_product_lower :
    (143738985473503 / 31250000000000 : ℝ) ≤ Real.pi * Real.exp (61 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell305_leftExp
    (by norm_num : (0 : ℝ) ≤ (366028397 / 250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell305_product_upper :
    Real.pi * Real.exp (153 / 400 : ℝ) ≤ (5756752694751149 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell305_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell305_endpointLower :
    (12543530859 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (61 / 320 : ℝ) (153 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (143738985473503 / 31250000000000 : ℝ) (Real.pi * Real.exp (61 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell305_product_lower
  have hD : Real.exp (Real.pi * Real.exp (153 / 400 : ℝ) - (61 / 640 : ℝ)) ≤
      (909299705449 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell305_denomUpper
    linarith [hpThetaJensenCell305_product_upper]
  have hi : (1 / (909299705449 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (153 / 400 : ℝ) - (61 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (909299705449 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (909299705449 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((61 / 640 : ℝ) - Real.pi * Real.exp (153 / 400 : ℝ)) := by
    rw [show (61 / 640 : ℝ) - Real.pi * Real.exp (153 / 400 : ℝ) =
      -(Real.pi * Real.exp (153 / 400 : ℝ) - (61 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (61 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (61 / 160 : ℝ)) := by
    have h := hpThetaJensenCell305_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (909299705449 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell305_endpointUpper :
    hpThetaJensenKernelEndpointUpper (61 / 320 : ℝ) (153 / 800 : ℝ) ≤ (2538490151 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (153 / 400 : ℝ)) (5756752694751149 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (153 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell305_product_upper
  have hD : (903799576253 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (61 / 160 : ℝ) - (153 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell305_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell305_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (61 / 160 : ℝ) - (153 / 1600 : ℝ)) ≤
      (1 / (903799576253 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (903799576253 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((153 / 1600 : ℝ) - Real.pi * Real.exp (61 / 160 : ℝ)) ≤
      (2 / (903799576253 / 10000000000 : ℝ) : ℝ) := by
    rw [show (153 / 1600 : ℝ) - Real.pi * Real.exp (61 / 160 : ℝ) =
      -(Real.pi * Real.exp (61 / 160 : ℝ) - (153 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (5756752694751149 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (5756752694751149 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell305_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (61 / 320 : ℝ) (153 / 800 : ℝ)) :
    (12543530859 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2538490151 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell305_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell305_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell306_leftExp :
    (14659448743 / 10000000000 : ℝ) ≤ Real.exp (153 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (153 / 400 : ℝ) (1012024849089 / 1000000000000 : ℝ)
    (14659448743 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell306_rightExp :
    Real.exp (307 / 800 : ℝ) ≤ (14677784513 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (307 / 800 : ℝ) (1012064382083 / 1000000000000 : ℝ)
    (14677784513 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell306_denomUpper :
    Real.exp (45155375081549209 / 10000000000000000 : ℝ) ≤ (57141684633 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (45155375081549209 / 10000000000000000 : ℝ)
    (1151551941711 / 1000000000000 : ℝ) (57141684633 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell306_denomLower :
    (908730238241 / 10000000000 : ℝ) ≤ Real.exp (5636828986927357 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5636828986927357 / 1250000000000000 : ℝ) (1151333372037
    / 1000000000000 : ℝ) (908730238241 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell306_product_lower :
    (5756750861927357 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (153 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell306_leftExp
    (by norm_num : (0 : ℝ) ≤ (14659448743 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell306_product_upper :
    Real.pi * Real.exp (307 / 800 : ℝ) ≤ (46111625081549209 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell306_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell306_endpointLower :
    (3128542361 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (153 / 800 : ℝ) (307 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5756750861927357 / 1250000000000000 : ℝ) (Real.pi * Real.exp (153 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell306_product_lower
  have hD : Real.exp (Real.pi * Real.exp (307 / 800 : ℝ) - (153 / 1600 : ℝ)) ≤
      (57141684633 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell306_denomUpper
    linarith [hpThetaJensenCell306_product_upper]
  have hi : (1 / (57141684633 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (307 / 800 : ℝ) - (153 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (57141684633 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (57141684633 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((153 / 1600 : ℝ) - Real.pi * Real.exp (307 / 800 : ℝ)) := by
    rw [show (153 / 1600 : ℝ) - Real.pi * Real.exp (307 / 800 : ℝ) =
      -(Real.pi * Real.exp (307 / 800 : ℝ) - (153 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (153 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (153 / 400 : ℝ)) := by
    have h := hpThetaJensenCell306_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (57141684633 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell306_endpointUpper :
    hpThetaJensenKernelEndpointUpper (153 / 800 : ℝ) (307 / 1600 : ℝ) ≤ (3165704431 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (307 / 800 : ℝ)) (46111625081549209 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (307 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell306_product_upper
  have hD : (908730238241 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (153 / 400 : ℝ) - (307 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell306_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell306_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (153 / 400 : ℝ) - (307 / 3200 : ℝ)) ≤
      (1 / (908730238241 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (908730238241 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((307 / 3200 : ℝ) - Real.pi * Real.exp (153 / 400 : ℝ)) ≤
      (2 / (908730238241 / 10000000000 : ℝ) : ℝ) := by
    rw [show (307 / 3200 : ℝ) - Real.pi * Real.exp (153 / 400 : ℝ) =
      -(Real.pi * Real.exp (153 / 400 : ℝ) - (307 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (46111625081549209 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (46111625081549209 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell306_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (153 / 800 : ℝ) (307 / 1600 : ℝ)) :
    (3128542361 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3165704431 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell306_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell306_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell307_leftExp :
    (14677784511 / 10000000000 : ℝ) ≤ Real.exp (307 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (307 / 800 : ℝ) (506032191041 / 500000000000 : ℝ)
    (14677784511 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell307_rightExp :
    Real.exp (77 / 200 : ℝ) ≤ (2939228643 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (77 / 200 : ℝ) (50605195831 / 50000000000 : ℝ)
    (2939228643 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell307_denomUpper :
    Real.exp (9041985130248299 / 2000000000000000 : ℝ) ≤ (459633980213 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9041985130248299 / 2000000000000000 : ℝ) (575874132057 /
    500000000000 : ℝ) (459633980213 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell307_denomLower :
    (228423593529 / 2500000000 : ℝ) ≤ Real.exp (5643638799685189 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5643638799685189 / 1250000000000000 : ℝ) (14394117473 /
    12500000000 : ℝ) (228423593529 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell307_product_lower :
    (5763951299685189 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (307 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell307_leftExp
    (by norm_num : (0 : ℝ) ≤ (14677784511 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell307_product_upper :
    Real.pi * Real.exp (77 / 200 : ℝ) ≤ (9233860130248299 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell307_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell307_endpointLower :
    (6242386417 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (307 / 1600 : ℝ) (77 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5763951299685189 / 1250000000000000 : ℝ) (Real.pi * Real.exp (307 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell307_product_lower
  have hD : Real.exp (Real.pi * Real.exp (77 / 200 : ℝ) - (307 / 3200 : ℝ)) ≤
      (459633980213 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell307_denomUpper
    linarith [hpThetaJensenCell307_product_upper]
  have hi : (1 / (459633980213 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (77 / 200 : ℝ) - (307 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (459633980213 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (459633980213 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((307 / 3200 : ℝ) - Real.pi * Real.exp (77 / 200 : ℝ)) := by
    rw [show (307 / 3200 : ℝ) - Real.pi * Real.exp (77 / 200 : ℝ) =
      -(Real.pi * Real.exp (77 / 200 : ℝ) - (307 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (307 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (307 / 800 : ℝ)) := by
    have h := hpThetaJensenCell307_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (459633980213 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell307_endpointUpper :
    hpThetaJensenKernelEndpointUpper (307 / 1600 : ℝ) (77 / 400 : ℝ) ≤ (197392951 / 156250000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (77 / 200 : ℝ)) (9233860130248299 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (77 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell307_product_upper
  have hD : (228423593529 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (307 / 800 : ℝ) - (77 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell307_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell307_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (307 / 800 : ℝ) - (77 / 800 : ℝ)) ≤
      (1 / (228423593529 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (228423593529 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((77 / 800 : ℝ) - Real.pi * Real.exp (307 / 800 : ℝ)) ≤
      (2 / (228423593529 / 2500000000 : ℝ) : ℝ) := by
    rw [show (77 / 800 : ℝ) - Real.pi * Real.exp (307 / 800 : ℝ) =
      -(Real.pi * Real.exp (307 / 800 : ℝ) - (77 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9233860130248299 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (9233860130248299 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell307_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (307 / 1600 : ℝ) (77 / 400 : ℝ)) :
    (6242386417 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (197392951 / 156250000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell307_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell307_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell308_leftExp :
    (7348071607 / 5000000000 : ℝ) ≤ Real.exp (77 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (77 / 200 : ℝ) (1012103916619 / 1000000000000 : ℝ)
    (7348071607 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell308_rightExp :
    Real.exp (309 / 800 : ℝ) ≤ (183931561 / 125000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (309 / 800 : ℝ) (1012143452701 / 1000000000000 : ℝ)
    (183931561 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell308_denomUpper :
    Real.exp (565806854516673 / 125000000000000 : ℝ) ≤ (924302990003 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (565806854516673 / 125000000000000 : ℝ) (1151944879681 /
    1000000000000 : ℝ) (924302990003 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell308_denomLower :
    (91869224703 / 1000000000 : ℝ) ≤ Real.exp (2825228809497293 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2825228809497293 / 625000000000000 : ℝ) (230345143269 /
    200000000000 : ℝ) (91869224703 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell308_product_lower :
    (2885580371997293 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (77 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell308_leftExp
    (by norm_num : (0 : ℝ) ≤ (7348071607 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell308_product_upper :
    Real.pi * Real.exp (309 / 800 : ℝ) ≤ (577838104516673 / 125000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell308_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell308_endpointLower :
    (12455341519 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (77 / 400 : ℝ) (309 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2885580371997293 / 625000000000000 : ℝ) (Real.pi * Real.exp (77 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell308_product_lower
  have hD : Real.exp (Real.pi * Real.exp (309 / 800 : ℝ) - (77 / 800 : ℝ)) ≤
      (924302990003 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell308_denomUpper
    linarith [hpThetaJensenCell308_product_upper]
  have hi : (1 / (924302990003 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (309 / 800 : ℝ) - (77 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (924302990003 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (924302990003 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((77 / 800 : ℝ) - Real.pi * Real.exp (309 / 800 : ℝ)) := by
    rw [show (77 / 800 : ℝ) - Real.pi * Real.exp (309 / 800 : ℝ) =
      -(Real.pi * Real.exp (309 / 800 : ℝ) - (77 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (77 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (77 / 200 : ℝ)) := by
    have h := hpThetaJensenCell308_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (924302990003 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell308_endpointUpper :
    hpThetaJensenKernelEndpointUpper (77 / 400 : ℝ) (309 / 1600 : ℝ) ≤ (12603444669 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (309 / 800 : ℝ)) (577838104516673 / 125000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (309 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell308_product_upper
  have hD : (91869224703 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (77 / 200 : ℝ) - (309 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell308_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell308_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (77 / 200 : ℝ) - (309 / 3200 : ℝ)) ≤
      (1 / (91869224703 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (91869224703 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((309 / 3200 : ℝ) - Real.pi * Real.exp (77 / 200 : ℝ)) ≤
      (2 / (91869224703 / 1000000000 : ℝ) : ℝ) := by
    rw [show (309 / 3200 : ℝ) - Real.pi * Real.exp (77 / 200 : ℝ) =
      -(Real.pi * Real.exp (77 / 200 : ℝ) - (309 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (577838104516673 / 125000000000000 : ℝ) ^ 2 - 6 *
      (577838104516673 / 125000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell308_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (77 / 400 : ℝ) (309 / 1600 : ℝ)) :
    (12455341519 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (12603444669 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell308_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell308_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell309_leftExp :
    (14714524879 / 10000000000 : ℝ) ≤ Real.exp (309 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (309 / 800 : ℝ) (10121434527 / 10000000000 : ℝ)
    (14714524879 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell309_rightExp :
    Real.exp (31 / 80 : ℝ) ≤ (14732929537 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (31 / 80 : ℝ) (1012182990327 / 1000000000000 : ℝ)
    (14732929537 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell309_denomUpper :
    Real.exp (45319243302932441 / 10000000000000000 : ℝ) ≤ (11617153881 / 125000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (45319243302932441 / 10000000000000000 : ℝ)
    (1152141788877 / 1000000000000 : ℝ) (11617153881 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell309_denomLower :
    (57732757599 / 625000000 : ℝ) ≤ Real.exp (5657285455458421 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5657285455458421 / 1250000000000000 : ℝ) (287980581999 /
    250000000000 : ℝ) (57732757599 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell309_product_lower :
    (5778379205458421 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (309 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell309_leftExp
    (by norm_num : (0 : ℝ) ≤ (14714524879 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell309_product_upper :
    Real.pi * Real.exp (31 / 80 : ℝ) ≤ (46284868302932441 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell309_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell309_endpointLower :
    (1242587599 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (309 / 1600 : ℝ) (31 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5778379205458421 / 1250000000000000 : ℝ) (Real.pi * Real.exp (309 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell309_product_lower
  have hD : Real.exp (Real.pi * Real.exp (31 / 80 : ℝ) - (309 / 3200 : ℝ)) ≤
      (11617153881 / 125000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell309_denomUpper
    linarith [hpThetaJensenCell309_product_upper]
  have hi : (1 / (11617153881 / 125000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (31 / 80 : ℝ) - (309 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (11617153881 / 125000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (11617153881 / 125000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((309 / 3200 : ℝ) - Real.pi * Real.exp (31 / 80 : ℝ)) := by
    rw [show (309 / 3200 : ℝ) - Real.pi * Real.exp (31 / 80 : ℝ) =
      -(Real.pi * Real.exp (31 / 80 : ℝ) - (309 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (309 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (309 / 800 : ℝ)) := by
    have h := hpThetaJensenCell309_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (11617153881 / 125000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell309_endpointUpper :
    hpThetaJensenKernelEndpointUpper (309 / 1600 : ℝ) (31 / 160 : ℝ) ≤ (3143426411 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (31 / 80 : ℝ)) (46284868302932441 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (31 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell309_product_upper
  have hD : (57732757599 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (309 / 800 : ℝ) - (31 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell309_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell309_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (309 / 800 : ℝ) - (31 / 320 : ℝ)) ≤
      (1 / (57732757599 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (57732757599 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((31 / 320 : ℝ) - Real.pi * Real.exp (309 / 800 : ℝ)) ≤
      (2 / (57732757599 / 625000000 : ℝ) : ℝ) := by
    rw [show (31 / 320 : ℝ) - Real.pi * Real.exp (309 / 800 : ℝ) =
      -(Real.pi * Real.exp (309 / 800 : ℝ) - (31 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (46284868302932441 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (46284868302932441 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell309_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (309 / 1600 : ℝ) (31 / 160 : ℝ)) :
    (1242587599 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3143426411 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell309_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell309_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell310_leftExp :
    (2946585907 / 2000000000 : ℝ) ≤ Real.exp (31 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (31 / 80 : ℝ) (506091495163 / 500000000000 : ℝ)
    (2946585907 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell310_rightExp :
    Real.exp (311 / 800 : ℝ) ≤ (7375678607 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (311 / 800 : ℝ) (1012222529497 / 1000000000000 : ℝ)
    (7375678607 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell310_denomUpper :
    Real.exp (22687005282000951 / 5000000000000000 : ℝ) ≤ (934476191581 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (22687005282000951 / 5000000000000000 : ℝ) (576169496079
    / 500000000000 : ℝ) (934476191581 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell310_denomLower :
    (2902469579 / 31250000 : ℝ) ≤ Real.exp (1132824464092993 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1132824464092993 / 250000000000000 : ℝ) (57605961663 /
    50000000000 : ℝ) (2902469579 / 31250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell310_product_lower :
    (1157121339092993 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (31 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell310_leftExp
    (by norm_num : (0 : ℝ) ≤ (2946585907 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell310_product_upper :
    Real.pi * Real.exp (311 / 800 : ℝ) ≤ (23171380282000951 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell310_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell310_endpointLower :
    (6198188371 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (31 / 160 : ℝ) (311 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1157121339092993 / 250000000000000 : ℝ) (Real.pi * Real.exp (31 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell310_product_lower
  have hD : Real.exp (Real.pi * Real.exp (311 / 800 : ℝ) - (31 / 320 : ℝ)) ≤
      (934476191581 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell310_denomUpper
    linarith [hpThetaJensenCell310_product_upper]
  have hi : (1 / (934476191581 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (311 / 800 : ℝ) - (31 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (934476191581 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (934476191581 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((31 / 320 : ℝ) - Real.pi * Real.exp (311 / 800 : ℝ)) := by
    rw [show (31 / 320 : ℝ) - Real.pi * Real.exp (311 / 800 : ℝ) =
      -(Real.pi * Real.exp (311 / 800 : ℝ) - (31 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (31 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (31 / 80 : ℝ)) := by
    have h := hpThetaJensenCell310_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (934476191581 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell310_endpointUpper :
    hpThetaJensenKernelEndpointUpper (31 / 160 : ℝ) (311 / 1600 : ℝ) ≤ (2508786457 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (311 / 800 : ℝ)) (23171380282000951 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (311 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell310_product_upper
  have hD : (2902469579 / 31250000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (31 / 80 : ℝ) - (311 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell310_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell310_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (31 / 80 : ℝ) - (311 / 3200 : ℝ)) ≤
      (1 / (2902469579 / 31250000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2902469579 / 31250000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((311 / 3200 : ℝ) - Real.pi * Real.exp (31 / 80 : ℝ)) ≤
      (2 / (2902469579 / 31250000 : ℝ) : ℝ) := by
    rw [show (311 / 3200 : ℝ) - Real.pi * Real.exp (31 / 80 : ℝ) =
      -(Real.pi * Real.exp (31 / 80 : ℝ) - (311 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (23171380282000951 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (23171380282000951 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell310_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (31 / 160 : ℝ) (311 / 1600 : ℝ)) :
    (6198188371 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2508786457 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell310_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell310_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell311_leftExp :
    (3687839303 / 2500000000 : ℝ) ≤ Real.exp (311 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (311 / 800 : ℝ) (126527816187 / 125000000000 : ℝ)
    (3687839303 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell311_rightExp :
    Real.exp (39 / 100 : ℝ) ≤ (14769807939 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (39 / 100 : ℝ) (253065517553 / 250000000000 : ℝ)
    (14769807939 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell311_denomUpper :
    Real.exp (45428850232506827 / 10000000000000000 : ℝ) ≤ (939614905439 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (45428850232506827 / 10000000000000000 : ℝ) (576268244991
    / 500000000000 : ℝ) (939614905439 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell311_denomLower :
    (466945474107 / 5000000000 : ℝ) ≤ Real.exp (1417742056448797 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1417742056448797 / 312500000000000 : ℝ) (576158216307 /
    500000000000 : ℝ) (466945474107 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell311_product_lower :
    (1448210806448797 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (311 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell311_leftExp
    (by norm_num : (0 : ℝ) ≤ (3687839303 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell311_product_upper :
    Real.pi * Real.exp (39 / 100 : ℝ) ≤ (46400725232506827 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell311_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell311_endpointLower :
    (494673771 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (311 / 1600 : ℝ) (39 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1448210806448797 / 312500000000000 : ℝ) (Real.pi * Real.exp (311 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell311_product_lower
  have hD : Real.exp (Real.pi * Real.exp (39 / 100 : ℝ) - (311 / 3200 : ℝ)) ≤
      (939614905439 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell311_denomUpper
    linarith [hpThetaJensenCell311_product_upper]
  have hi : (1 / (939614905439 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (39 / 100 : ℝ) - (311 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (939614905439 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (939614905439 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((311 / 3200 : ℝ) - Real.pi * Real.exp (39 / 100 : ℝ)) := by
    rw [show (311 / 3200 : ℝ) - Real.pi * Real.exp (39 / 100 : ℝ) =
      -(Real.pi * Real.exp (39 / 100 : ℝ) - (311 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (311 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (311 / 800 : ℝ)) := by
    have h := hpThetaJensenCell311_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (939614905439 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell311_endpointUpper :
    hpThetaJensenKernelEndpointUpper (311 / 1600 : ℝ) (39 / 200 : ℝ) ≤ (6257062541 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (39 / 100 : ℝ)) (46400725232506827 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (39 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell311_product_upper
  have hD : (466945474107 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (311 / 800 : ℝ) - (39 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell311_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell311_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (311 / 800 : ℝ) - (39 / 400 : ℝ)) ≤
      (1 / (466945474107 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (466945474107 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((39 / 400 : ℝ) - Real.pi * Real.exp (311 / 800 : ℝ)) ≤
      (2 / (466945474107 / 5000000000 : ℝ) : ℝ) := by
    rw [show (39 / 400 : ℝ) - Real.pi * Real.exp (311 / 800 : ℝ) =
      -(Real.pi * Real.exp (311 / 800 : ℝ) - (39 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (46400725232506827 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (46400725232506827 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell311_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (311 / 1600 : ℝ) (39 / 200 : ℝ)) :
    (494673771 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6257062541 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell311_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell311_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell312_leftExp :
    (7384903969 / 5000000000 : ℝ) ≤ Real.exp (39 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (39 / 100 : ℝ) (1012262070211 / 1000000000000 : ℝ)
    (7384903969 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell312_rightExp :
    Real.exp (313 / 800 : ℝ) ≤ (14788281743 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (313 / 800 : ℝ) (126537701559 / 125000000000 : ℝ)
    (14788281743 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell312_denomUpper :
    Real.exp (45483762405836599 / 10000000000000000 : ℝ) ≤ (47239436369 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (45483762405836599 / 10000000000000000 : ℝ) (576367141419
    / 500000000000 : ℝ) (47239436369 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell312_denomLower :
    (58689152647 / 625000000 : ℝ) ≤ Real.exp (2838911591222331 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2838911591222331 / 625000000000000 : ℝ) (288128481629 /
    250000000000 : ℝ) (58689152647 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell312_product_lower :
    (2900044403722331 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (39 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell312_leftExp
    (by norm_num : (0 : ℝ) ≤ (7384903969 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell312_product_upper :
    Real.pi * Real.exp (313 / 800 : ℝ) ≤ (46458762405836599 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell312_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell312_endpointLower :
    (385539971 / 312500000 : ℝ) ≤ hpThetaTraceEndpointLower (39 / 200 : ℝ) (313 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2900044403722331 / 625000000000000 : ℝ) (Real.pi * Real.exp (39 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell312_product_lower
  have hD : Real.exp (Real.pi * Real.exp (313 / 800 : ℝ) - (39 / 400 : ℝ)) ≤
      (47239436369 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell312_denomUpper
    linarith [hpThetaJensenCell312_product_upper]
  have hi : (1 / (47239436369 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (313 / 800 : ℝ) - (39 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (47239436369 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (47239436369 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((39 / 400 : ℝ) - Real.pi * Real.exp (313 / 800 : ℝ)) := by
    rw [show (39 / 400 : ℝ) - Real.pi * Real.exp (313 / 800 : ℝ) =
      -(Real.pi * Real.exp (313 / 800 : ℝ) - (39 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (39 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (39 / 100 : ℝ)) := by
    have h := hpThetaJensenCell312_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (47239436369 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell312_endpointUpper :
    hpThetaJensenKernelEndpointUpper (39 / 200 : ℝ) (313 / 1600 : ℝ) ≤ (12484284541 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (313 / 800 : ℝ)) (46458762405836599 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (313 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell312_product_upper
  have hD : (58689152647 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (39 / 100 : ℝ) - (313 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell312_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell312_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (39 / 100 : ℝ) - (313 / 3200 : ℝ)) ≤
      (1 / (58689152647 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (58689152647 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((313 / 3200 : ℝ) - Real.pi * Real.exp (39 / 100 : ℝ)) ≤
      (2 / (58689152647 / 625000000 : ℝ) : ℝ) := by
    rw [show (313 / 3200 : ℝ) - Real.pi * Real.exp (39 / 100 : ℝ) =
      -(Real.pi * Real.exp (39 / 100 : ℝ) - (313 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (46458762405836599 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (46458762405836599 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell312_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (39 / 200 : ℝ) (313 / 1600 : ℝ)) :
    (385539971 / 312500000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (12484284541 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell312_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell312_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell313_leftExp :
    (7394140871 / 5000000000 : ℝ) ≤ Real.exp (313 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (313 / 800 : ℝ) (1012301612471 / 1000000000000 : ℝ)
    (7394140871 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell313_rightExp :
    Real.exp (157 / 400 : ℝ) ≤ (7403389327 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (157 / 400 : ℝ) (253085289069 / 250000000000 : ℝ)
    (7403389327 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell313_denomUpper :
    Real.exp (22769373585977911 / 5000000000000000 : ℝ) ≤ (949997934329 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (22769373585977911 / 5000000000000000 : ℝ) (72058273199 /
    62500000000 : ℝ) (949997934329 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell313_denomLower :
    (472098511151 / 5000000000 : ℝ) ≤ Real.exp (2842343600900829 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2842343600900829 / 625000000000000 : ℝ) (576355857717 /
    500000000000 : ℝ) (472098511151 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell313_product_lower :
    (2903671725900829 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (313 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell313_leftExp
    (by norm_num : (0 : ℝ) ≤ (7394140871 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell313_product_upper :
    Real.pi * Real.exp (157 / 400 : ℝ) ≤ (23258436085977911 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell313_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell313_endpointLower :
    (1230768163 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (313 / 1600 : ℝ) (157 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2903671725900829 / 625000000000000 : ℝ) (Real.pi * Real.exp (313 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell313_product_lower
  have hD : Real.exp (Real.pi * Real.exp (157 / 400 : ℝ) - (313 / 3200 : ℝ)) ≤
      (949997934329 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell313_denomUpper
    linarith [hpThetaJensenCell313_product_upper]
  have hi : (1 / (949997934329 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (157 / 400 : ℝ) - (313 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (949997934329 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (949997934329 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((313 / 3200 : ℝ) - Real.pi * Real.exp (157 / 400 : ℝ)) := by
    rw [show (313 / 3200 : ℝ) - Real.pi * Real.exp (157 / 400 : ℝ) =
      -(Real.pi * Real.exp (157 / 400 : ℝ) - (313 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (313 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (313 / 800 : ℝ)) := by
    have h := hpThetaJensenCell313_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (949997934329 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell313_endpointUpper :
    hpThetaJensenKernelEndpointUpper (313 / 1600 : ℝ) (157 / 800 : ℝ) ≤ (3113602789 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (157 / 400 : ℝ)) (23258436085977911 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (157 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell313_product_upper
  have hD : (472098511151 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (313 / 800 : ℝ) - (157 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell313_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell313_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (313 / 800 : ℝ) - (157 / 1600 : ℝ)) ≤
      (1 / (472098511151 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (472098511151 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((157 / 1600 : ℝ) - Real.pi * Real.exp (313 / 800 : ℝ)) ≤
      (2 / (472098511151 / 5000000000 : ℝ) : ℝ) := by
    rw [show (157 / 1600 : ℝ) - Real.pi * Real.exp (313 / 800 : ℝ) =
      -(Real.pi * Real.exp (313 / 800 : ℝ) - (157 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (23258436085977911 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (23258436085977911 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell313_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (313 / 1600 : ℝ) (157 / 800 : ℝ)) :
    (1230768163 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3113602789 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell313_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell313_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell314_leftExp :
    (3701694663 / 2500000000 : ℝ) ≤ Real.exp (157 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (157 / 400 : ℝ) (40493646251 / 40000000000 : ℝ)
    (3701694663 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell314_rightExp :
    Real.exp (63 / 160 : ℝ) ≤ (14825298699 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (63 / 160 : ℝ) (126547587703 / 125000000000 : ℝ)
    (14825298699 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell314_denomUpper :
    Real.exp (45593804615687507 / 10000000000000000 : ℝ) ≤ (955242805319 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (45593804615687507 / 10000000000000000 : ℝ) (576565377733
    / 500000000000 : ℝ) (955242805319 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell314_denomLower :
    (949402964733 / 10000000000 : ℝ) ≤ Real.exp (1422890073715437 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1422890073715437 / 312500000000000 : ℝ) (1152909799823 /
    1000000000000 : ℝ) (949402964733 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell314_product_lower :
    (1453651792465437 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (157 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell314_leftExp
    (by norm_num : (0 : ℝ) ≤ (3701694663 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell314_product_upper :
    Real.pi * Real.exp (63 / 160 : ℝ) ≤ (46575054615687507 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell314_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell314_endpointLower :
    (12278052449 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (157 / 800 : ℝ) (63 / 320 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1453651792465437 / 312500000000000 : ℝ) (Real.pi * Real.exp (157 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell314_product_lower
  have hD : Real.exp (Real.pi * Real.exp (63 / 160 : ℝ) - (157 / 1600 : ℝ)) ≤
      (955242805319 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell314_denomUpper
    linarith [hpThetaJensenCell314_product_upper]
  have hi : (1 / (955242805319 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (63 / 160 : ℝ) - (157 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (955242805319 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (955242805319 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((157 / 1600 : ℝ) - Real.pi * Real.exp (63 / 160 : ℝ)) := by
    rw [show (157 / 1600 : ℝ) - Real.pi * Real.exp (63 / 160 : ℝ) =
      -(Real.pi * Real.exp (63 / 160 : ℝ) - (157 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (157 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (157 / 400 : ℝ)) := by
    have h := hpThetaJensenCell314_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (955242805319 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell314_endpointUpper :
    hpThetaJensenKernelEndpointUpper (157 / 800 : ℝ) (63 / 320 : ℝ) ≤ (496980217 / 400000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (63 / 160 : ℝ)) (46575054615687507 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (63 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell314_product_upper
  have hD : (949402964733 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (157 / 400 : ℝ) - (63 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell314_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell314_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (157 / 400 : ℝ) - (63 / 640 : ℝ)) ≤
      (1 / (949402964733 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (949402964733 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((63 / 640 : ℝ) - Real.pi * Real.exp (157 / 400 : ℝ)) ≤
      (2 / (949402964733 / 10000000000 : ℝ) : ℝ) := by
    rw [show (63 / 640 : ℝ) - Real.pi * Real.exp (157 / 400 : ℝ) =
      -(Real.pi * Real.exp (157 / 400 : ℝ) - (63 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (46575054615687507 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (46575054615687507 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell314_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (157 / 800 : ℝ) (63 / 320 : ℝ)) :
    (12278052449 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (496980217 / 400000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell314_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell314_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell315_leftExp :
    (7412649349 / 5000000000 : ℝ) ≤ Real.exp (63 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (63 / 160 : ℝ) (1012380701623 / 1000000000000 : ℝ)
    (7412649349 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell315_rightExp :
    Real.exp (79 / 200 : ℝ) ≤ (1484384191 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (79 / 200 : ℝ) (506210124259 / 500000000000 : ℝ)
    (1484384191 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell315_denomUpper :
    Real.exp (4564893483756263 / 1000000000000000 : ℝ) ≤ (960523623369 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4564893483756263 / 1000000000000000 : ℝ) (288332359047 /
    250000000000 : ℝ) (960523623369 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell315_denomLower :
    (954644549477 / 10000000000 : ℝ) ≤ Real.exp (2849221236702951 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2849221236702951 / 625000000000000 : ℝ) (576554090083 /
    500000000000 : ℝ) (954644549477 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell315_product_lower :
    (2910939986702951 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (63 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell315_leftExp
    (by norm_num : (0 : ℝ) ≤ (7412649349 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell315_product_upper :
    Real.pi * Real.exp (79 / 200 : ℝ) ≤ (4663330983756263 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell315_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell315_endpointLower :
    (12248392011 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (63 / 320 : ℝ) (79 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2910939986702951 / 625000000000000 : ℝ) (Real.pi * Real.exp (63 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell315_product_lower
  have hD : Real.exp (Real.pi * Real.exp (79 / 200 : ℝ) - (63 / 640 : ℝ)) ≤
      (960523623369 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell315_denomUpper
    linarith [hpThetaJensenCell315_product_upper]
  have hi : (1 / (960523623369 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (79 / 200 : ℝ) - (63 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (960523623369 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (960523623369 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((63 / 640 : ℝ) - Real.pi * Real.exp (79 / 200 : ℝ)) := by
    rw [show (63 / 640 : ℝ) - Real.pi * Real.exp (79 / 200 : ℝ) =
      -(Real.pi * Real.exp (79 / 200 : ℝ) - (63 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (63 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (63 / 160 : ℝ)) := by
    have h := hpThetaJensenCell315_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (960523623369 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell315_endpointUpper :
    hpThetaJensenKernelEndpointUpper (63 / 320 : ℝ) (79 / 400 : ℝ) ≤ (1549320981 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (79 / 200 : ℝ)) (4663330983756263 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (79 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell315_product_upper
  have hD : (954644549477 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (63 / 160 : ℝ) - (79 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell315_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell315_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (63 / 160 : ℝ) - (79 / 800 : ℝ)) ≤
      (1 / (954644549477 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (954644549477 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((79 / 800 : ℝ) - Real.pi * Real.exp (63 / 160 : ℝ)) ≤
      (2 / (954644549477 / 10000000000 : ℝ) : ℝ) := by
    rw [show (79 / 800 : ℝ) - Real.pi * Real.exp (63 / 160 : ℝ) =
      -(Real.pi * Real.exp (63 / 160 : ℝ) - (79 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4663330983756263 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (4663330983756263 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell315_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (63 / 320 : ℝ) (79 / 400 : ℝ)) :
    (12248392011 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1549320981 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell315_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell315_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell316_leftExp :
    (3710960477 / 2500000000 : ℝ) ≤ Real.exp (79 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (79 / 200 : ℝ) (1012420248517 / 1000000000000 : ℝ)
    (3710960477 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell316_rightExp :
    Real.exp (317 / 800 : ℝ) ≤ (7431204157 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (317 / 800 : ℝ) (253114949239 / 250000000000 : ℝ)
    (7431204157 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell316_denomUpper :
    Real.exp (22852068961202101 / 5000000000000000 : ℝ) ≤ (482920336221 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (22852068961202101 / 5000000000000000 : ℝ) (288382103449
    / 250000000000 : ℝ) (482920336221 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell316_denomLower :
    (479961029067 / 5000000000 : ℝ) ≤ Real.exp (1426333437107423 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1426333437107423 / 312500000000000 : ℝ) (28832671423 /
    25000000000 : ℝ) (479961029067 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell316_product_lower :
    (1457290468357423 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (79 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell316_leftExp
    (by norm_num : (0 : ℝ) ≤ (3710960477 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell316_product_upper :
    Real.pi * Real.exp (317 / 800 : ℝ) ≤ (23345818961202101 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell316_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell316_endpointLower :
    (763668801 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (79 / 400 : ℝ) (317 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1457290468357423 / 312500000000000 : ℝ) (Real.pi * Real.exp (79 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell316_product_lower
  have hD : Real.exp (Real.pi * Real.exp (317 / 800 : ℝ) - (79 / 800 : ℝ)) ≤
      (482920336221 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell316_denomUpper
    linarith [hpThetaJensenCell316_product_upper]
  have hi : (1 / (482920336221 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (317 / 800 : ℝ) - (79 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (482920336221 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (482920336221 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((79 / 800 : ℝ) - Real.pi * Real.exp (317 / 800 : ℝ)) := by
    rw [show (79 / 800 : ℝ) - Real.pi * Real.exp (317 / 800 : ℝ) =
      -(Real.pi * Real.exp (317 / 800 : ℝ) - (79 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (79 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (79 / 200 : ℝ)) := by
    have h := hpThetaJensenCell316_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (482920336221 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell316_endpointUpper :
    hpThetaJensenKernelEndpointUpper (79 / 400 : ℝ) (317 / 1600 : ℝ) ≤ (309114973 / 250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (317 / 800 : ℝ)) (23345818961202101 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (317 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell316_product_upper
  have hD : (479961029067 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (79 / 200 : ℝ) - (317 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell316_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell316_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (79 / 200 : ℝ) - (317 / 3200 : ℝ)) ≤
      (1 / (479961029067 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (479961029067 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((317 / 3200 : ℝ) - Real.pi * Real.exp (79 / 200 : ℝ)) ≤
      (2 / (479961029067 / 5000000000 : ℝ) : ℝ) := by
    rw [show (317 / 3200 : ℝ) - Real.pi * Real.exp (79 / 200 : ℝ) =
      -(Real.pi * Real.exp (79 / 200 : ℝ) - (317 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (23345818961202101 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (23345818961202101 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell316_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (79 / 400 : ℝ) (317 / 1600 : ℝ)) :
    (763668801 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (309114973 / 250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell316_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell316_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell317_leftExp :
    (1857801039 / 1250000000 : ℝ) ≤ Real.exp (317 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (317 / 800 : ℝ) (202491959391 / 200000000000 : ℝ)
    (1857801039 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell317_rightExp :
    Real.exp (159 / 400 : ℝ) ≤ (14880997941 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (159 / 400 : ℝ) (50624967347 / 50000000000 : ℝ)
    (14880997941 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell317_denomUpper :
    Real.exp (45759413964460013 / 10000000000000000 : ℝ) ≤ (194238847997 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (45759413964460013 / 10000000000000000 : ℝ)
    (1153727688773 / 1000000000000 : ℝ) (194238847997 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell317_denomLower :
    (965235775417 / 10000000000 : ℝ) ≤ Real.exp (714029266464261 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (714029266464261 / 156250000000000 : ℝ) (576752915283 /
    500000000000 : ℝ) (965235775417 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell317_product_lower :
    (729556610214261 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (317 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell317_leftExp
    (by norm_num : (0 : ℝ) ≤ (1857801039 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell317_product_upper :
    Real.pi * Real.exp (159 / 400 : ℝ) ≤ (46750038964460013 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell317_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell317_endpointLower :
    (6094489677 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (317 / 1600 : ℝ) (159 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (729556610214261 / 156250000000000 : ℝ) (Real.pi * Real.exp (317 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell317_product_lower
  have hD : Real.exp (Real.pi * Real.exp (159 / 400 : ℝ) - (317 / 3200 : ℝ)) ≤
      (194238847997 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell317_denomUpper
    linarith [hpThetaJensenCell317_product_upper]
  have hi : (1 / (194238847997 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (159 / 400 : ℝ) - (317 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (194238847997 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (194238847997 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((317 / 3200 : ℝ) - Real.pi * Real.exp (159 / 400 : ℝ)) := by
    rw [show (317 / 3200 : ℝ) - Real.pi * Real.exp (159 / 400 : ℝ) =
      -(Real.pi * Real.exp (159 / 400 : ℝ) - (317 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (317 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (317 / 800 : ℝ)) := by
    have h := hpThetaJensenCell317_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (194238847997 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell317_endpointUpper :
    hpThetaJensenKernelEndpointUpper (317 / 1600 : ℝ) (159 / 800 : ℝ) ≤ (12334599139 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (159 / 400 : ℝ)) (46750038964460013 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (159 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell317_product_upper
  have hD : (965235775417 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (317 / 800 : ℝ) - (159 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell317_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell317_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (317 / 800 : ℝ) - (159 / 1600 : ℝ)) ≤
      (1 / (965235775417 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (965235775417 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((159 / 1600 : ℝ) - Real.pi * Real.exp (317 / 800 : ℝ)) ≤
      (2 / (965235775417 / 10000000000 : ℝ) : ℝ) := by
    rw [show (159 / 1600 : ℝ) - Real.pi * Real.exp (317 / 800 : ℝ) =
      -(Real.pi * Real.exp (317 / 800 : ℝ) - (159 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (46750038964460013 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (46750038964460013 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell317_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (317 / 1600 : ℝ) (159 / 800 : ℝ)) :
    (6094489677 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (12334599139 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell317_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell317_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell318_leftExp :
    (14880997939 / 10000000000 : ℝ) ≤ Real.exp (159 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (159 / 400 : ℝ) (1012499346939 / 1000000000000 : ℝ)
    (14880997939 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell318_rightExp :
    Real.exp (319 / 800 : ℝ) ≤ (14899610819 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (319 / 800 : ℝ) (253134724617 / 250000000000 : ℝ)
    (14899610819 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell318_denomUpper :
    Real.exp (45814763051694667 / 10000000000000000 : ℝ) ≤ (976584615301 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (45814763051694667 / 10000000000000000 : ℝ)
    (1153927261577 / 1000000000000 : ℝ) (976584615301 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell318_denomLower :
    (970585988249 / 10000000000 : ℝ) ≤ Real.exp (5719143634647361 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5719143634647361 / 1250000000000000 : ℝ) (576852550787 /
    500000000000 : ℝ) (970585988249 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell318_product_lower :
    (5843753009647361 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (159 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell318_leftExp
    (by norm_num : (0 : ℝ) ≤ (14880997939 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell318_product_upper :
    Real.pi * Real.exp (319 / 800 : ℝ) ≤ (46808513051694667 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell318_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell318_endpointLower :
    (3039807031 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (159 / 800 : ℝ) (319 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5843753009647361 / 1250000000000000 : ℝ) (Real.pi * Real.exp (159 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell318_product_lower
  have hD : Real.exp (Real.pi * Real.exp (319 / 800 : ℝ) - (159 / 1600 : ℝ)) ≤
      (976584615301 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell318_denomUpper
    linarith [hpThetaJensenCell318_product_upper]
  have hi : (1 / (976584615301 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (319 / 800 : ℝ) - (159 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (976584615301 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (976584615301 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((159 / 1600 : ℝ) - Real.pi * Real.exp (319 / 800 : ℝ)) := by
    rw [show (159 / 1600 : ℝ) - Real.pi * Real.exp (319 / 800 : ℝ) =
      -(Real.pi * Real.exp (319 / 800 : ℝ) - (159 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (159 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (159 / 400 : ℝ)) := by
    have h := hpThetaJensenCell318_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (976584615301 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell318_endpointUpper :
    hpThetaJensenKernelEndpointUpper (159 / 800 : ℝ) (319 / 1600 : ℝ) ≤ (6152284499 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (319 / 800 : ℝ)) (46808513051694667 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (319 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell318_product_upper
  have hD : (970585988249 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (159 / 400 : ℝ) - (319 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell318_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell318_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (159 / 400 : ℝ) - (319 / 3200 : ℝ)) ≤
      (1 / (970585988249 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (970585988249 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((319 / 3200 : ℝ) - Real.pi * Real.exp (159 / 400 : ℝ)) ≤
      (2 / (970585988249 / 10000000000 : ℝ) : ℝ) := by
    rw [show (319 / 3200 : ℝ) - Real.pi * Real.exp (159 / 400 : ℝ) =
      -(Real.pi * Real.exp (159 / 400 : ℝ) - (319 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (46808513051694667 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (46808513051694667 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell318_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (159 / 800 : ℝ) (319 / 1600 : ℝ)) :
    (3039807031 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6152284499 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell318_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell318_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell319_leftExp :
    (14899610817 / 10000000000 : ℝ) ≤ Real.exp (319 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (319 / 800 : ℝ) (1012538898467 / 1000000000000 : ℝ)
    (14899610817 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell319_rightExp :
    Real.exp (2 / 5 : ℝ) ≤ (14918246977 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (2 / 5 : ℝ) (1012578451541 / 1000000000000 : ℝ)
    (14918246977 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell319_denomUpper :
    Real.exp (45870185275214361 / 10000000000000000 : ℝ) ≤ (245503022661 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (45870185275214361 / 10000000000000000 : ℝ)
    (1154127132681 / 1000000000000 : ℝ) (245503022661 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell319_denomLower :
    (975972985803 / 10000000000 : ℝ) ≤ Real.exp (5726062268225083 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5726062268225083 / 1250000000000000 : ℝ) (288476167601 /
    250000000000 : ℝ) (975972985803 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell319_product_lower :
    (5851062268225083 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (319 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell319_leftExp
    (by norm_num : (0 : ℝ) ≤ (14899610817 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell319_product_upper :
    Real.pi * Real.exp (2 / 5 : ℝ) ≤ (46867060275214361 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell319_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell319_endpointLower :
    (189522619 / 156250000 : ℝ) ≤ hpThetaTraceEndpointLower (319 / 1600 : ℝ) (1 / 5 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5851062268225083 / 1250000000000000 : ℝ) (Real.pi * Real.exp (319 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell319_product_lower
  have hD : Real.exp (Real.pi * Real.exp (2 / 5 : ℝ) - (319 / 3200 : ℝ)) ≤
      (245503022661 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell319_denomUpper
    linarith [hpThetaJensenCell319_product_upper]
  have hi : (1 / (245503022661 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (2 / 5 : ℝ) - (319 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (245503022661 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (245503022661 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((319 / 3200 : ℝ) - Real.pi * Real.exp (2 / 5 : ℝ)) := by
    rw [show (319 / 3200 : ℝ) - Real.pi * Real.exp (2 / 5 : ℝ) =
      -(Real.pi * Real.exp (2 / 5 : ℝ) - (319 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (319 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (319 / 800 : ℝ)) := by
    have h := hpThetaJensenCell319_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (245503022661 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell319_endpointUpper :
    hpThetaJensenKernelEndpointUpper (319 / 1600 : ℝ) (1 / 5 : ℝ) ≤ (12274508999 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (2 / 5 : ℝ)) (46867060275214361 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1 / 5 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell319_product_upper
  have hD : (975972985803 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (319 / 800 : ℝ) - (1 / 10 : ℝ)) := by
    apply le_trans hpThetaJensenCell319_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell319_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (319 / 800 : ℝ) - (1 / 10 : ℝ)) ≤
      (1 / (975972985803 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (975972985803 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1 / 10 : ℝ) - Real.pi * Real.exp (319 / 800 : ℝ)) ≤
      (2 / (975972985803 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1 / 10 : ℝ) - Real.pi * Real.exp (319 / 800 : ℝ) =
      -(Real.pi * Real.exp (319 / 800 : ℝ) - (1 / 10 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (46867060275214361 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (46867060275214361 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell319_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (319 / 1600 : ℝ) (1 / 5 : ℝ)) :
    (189522619 / 156250000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (12274508999 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell319_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell319_endpointUpper

def hpThetaJensenCellsBatch015Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (507591707 / 400000000 : ℝ)
  | 1 => (24727763 / 19531250 : ℝ)
  | 2 => (12631398969 / 10000000000 : ℝ)
  | 3 => (6301073057 / 5000000000 : ℝ)
  | 4 => (628642829 / 500000000 : ℝ)
  | 5 => (12543530859 / 10000000000 : ℝ)
  | 6 => (3128542361 / 2500000000 : ℝ)
  | 7 => (6242386417 / 5000000000 : ℝ)
  | 8 => (12455341519 / 10000000000 : ℝ)
  | 9 => (1242587599 / 1000000000 : ℝ)
  | 10 => (6198188371 / 5000000000 : ℝ)
  | 11 => (494673771 / 400000000 : ℝ)
  | 12 => (385539971 / 312500000 : ℝ)
  | 13 => (1230768163 / 1000000000 : ℝ)
  | 14 => (12278052449 / 10000000000 : ℝ)
  | 15 => (12248392011 / 10000000000 : ℝ)
  | 16 => (763668801 / 625000000 : ℝ)
  | 17 => (6094489677 / 5000000000 : ℝ)
  | 18 => (3039807031 / 2500000000 : ℝ)
  | 19 => (189522619 / 156250000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch015Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (6420030529 / 5000000000 : ℝ)
  | 1 => (12810614637 / 10000000000 : ℝ)
  | 2 => (12781129901 / 10000000000 : ℝ)
  | 3 => (12751607339 / 10000000000 : ℝ)
  | 4 => (12722047459 / 10000000000 : ℝ)
  | 5 => (2538490151 / 2000000000 : ℝ)
  | 6 => (3165704431 / 2500000000 : ℝ)
  | 7 => (197392951 / 156250000 : ℝ)
  | 8 => (12603444669 / 10000000000 : ℝ)
  | 9 => (3143426411 / 2500000000 : ℝ)
  | 10 => (2508786457 / 2000000000 : ℝ)
  | 11 => (6257062541 / 5000000000 : ℝ)
  | 12 => (12484284541 / 10000000000 : ℝ)
  | 13 => (3113602789 / 2500000000 : ℝ)
  | 14 => (496980217 / 400000000 : ℝ)
  | 15 => (1549320981 / 1250000000 : ℝ)
  | 16 => (309114973 / 250000000 : ℝ)
  | 17 => (12334599139 / 10000000000 : ℝ)
  | 18 => (6152284499 / 5000000000 : ℝ)
  | 19 => (12274508999 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch015_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((300 : ℝ) + (j.val : ℝ)) / 1600)
      (((300 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch015Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch015Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell300_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell301_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell302_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell303_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell304_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell305_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell306_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell307_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell308_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell309_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell310_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell311_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell312_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell313_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell314_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell315_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell316_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell317_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell318_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell319_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper] at h ⊢
    exact h

end HodgeProofHP
