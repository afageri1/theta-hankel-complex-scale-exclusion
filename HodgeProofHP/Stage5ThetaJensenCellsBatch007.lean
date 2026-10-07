import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell140_leftExp :
    (2382492433 / 2000000000 : ℝ) ≤ Real.exp (7 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7 / 40 : ℝ) (1005483730909 / 1000000000000 : ℝ)
    (2382492433 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell140_rightExp :
    Real.exp (141 / 800 : ℝ) ≤ (2385472411 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (141 / 800 : ℝ) (502761504193 / 500000000000 : ℝ)
    (2385472411 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell140_denomUpper :
    Real.exp (7406683428090723 / 2000000000000000 : ℝ) ≤ (405826937763 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7406683428090723 / 2000000000000000 : ℝ) (1122692062631
    / 1000000000000 : ℝ) (405826937763 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell140_denomLower :
    (403805035771 / 10000000000 : ℝ) ≤ Real.exp (924586770946667 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (924586770946667 / 250000000000000 : ℝ) (561258422031 /
    500000000000 : ℝ) (403805035771 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell140_product_lower :
    (935602395946667 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (7 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell140_leftExp
    (by norm_num : (0 : ℝ) ≤ (2382492433 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell140_product_upper :
    Real.pi * Real.exp (141 / 800 : ℝ) ≤ (7494183428090723 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell140_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell140_endpointLower :
    (16543042043 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (7 / 80 : ℝ) (141 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (935602395946667 / 250000000000000 : ℝ) (Real.pi * Real.exp (7 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell140_product_lower
  have hD : Real.exp (Real.pi * Real.exp (141 / 800 : ℝ) - (7 / 160 : ℝ)) ≤
      (405826937763 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell140_denomUpper
    linarith [hpThetaJensenCell140_product_upper]
  have hi : (1 / (405826937763 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (141 / 800 : ℝ) - (7 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (405826937763 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (405826937763 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((7 / 160 : ℝ) - Real.pi * Real.exp (141 / 800 : ℝ)) := by
    rw [show (7 / 160 : ℝ) - Real.pi * Real.exp (141 / 800 : ℝ) =
      -(Real.pi * Real.exp (141 / 800 : ℝ) - (7 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (7 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (7 / 40 : ℝ)) := by
    have h := hpThetaJensenCell140_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (405826937763 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell140_endpointUpper :
    hpThetaJensenKernelEndpointUpper (7 / 80 : ℝ) (141 / 1600 : ℝ) ≤ (16725364879 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (141 / 800 : ℝ)) (7494183428090723 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (141 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell140_product_upper
  have hD : (403805035771 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (7 / 40 : ℝ) - (141 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell140_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell140_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (7 / 40 : ℝ) - (141 / 3200 : ℝ)) ≤
      (1 / (403805035771 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (403805035771 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((141 / 3200 : ℝ) - Real.pi * Real.exp (7 / 40 : ℝ)) ≤
      (2 / (403805035771 / 10000000000 : ℝ) : ℝ) := by
    rw [show (141 / 3200 : ℝ) - Real.pi * Real.exp (7 / 40 : ℝ) =
      -(Real.pi * Real.exp (7 / 40 : ℝ) - (141 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (7494183428090723 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (7494183428090723 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell140_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (7 / 80 : ℝ) (141 / 1600 : ℝ)) :
    (16543042043 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (16725364879 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell140_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell140_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell141_leftExp :
    (5963681027 / 5000000000 : ℝ) ≤ Real.exp (141 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (141 / 800 : ℝ) (201104601677 / 200000000000 : ℝ)
    (5963681027 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell141_rightExp :
    Real.exp (71 / 400 : ℝ) ≤ (597114029 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (71 / 400 : ℝ) (201112457479 / 200000000000 : ℝ)
    (597114029 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell141_denomUpper :
    Real.exp (1853858003708197 / 500000000000000 : ℝ) ≤ (407606032153 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1853858003708197 / 500000000000000 : ℝ) (224569108277 /
    200000000000 : ℝ) (407606032153 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell141_denomLower :
    (202786445643 / 5000000000 : ℝ) ≤ Real.exp (2314197200621873 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2314197200621873 / 625000000000000 : ℝ) (35083440419 /
    31250000000 : ℝ) (202786445643 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell141_product_lower :
    (2341931575621873 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (141 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell141_leftExp
    (by norm_num : (0 : ℝ) ≤ (5963681027 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell141_product_upper :
    Real.pi * Real.exp (71 / 400 : ℝ) ≤ (1875889253708197 / 500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell141_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell141_endpointLower :
    (1032866411 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (141 / 1600 : ℝ) (71 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2341931575621873 / 625000000000000 : ℝ) (Real.pi * Real.exp (141 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell141_product_lower
  have hD : Real.exp (Real.pi * Real.exp (71 / 400 : ℝ) - (141 / 3200 : ℝ)) ≤
      (407606032153 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell141_denomUpper
    linarith [hpThetaJensenCell141_product_upper]
  have hi : (1 / (407606032153 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (71 / 400 : ℝ) - (141 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (407606032153 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (407606032153 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((141 / 3200 : ℝ) - Real.pi * Real.exp (71 / 400 : ℝ)) := by
    rw [show (141 / 3200 : ℝ) - Real.pi * Real.exp (71 / 400 : ℝ) =
      -(Real.pi * Real.exp (71 / 400 : ℝ) - (141 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (141 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (141 / 800 : ℝ)) := by
    have h := hpThetaJensenCell141_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (407606032153 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell141_endpointUpper :
    hpThetaJensenKernelEndpointUpper (141 / 1600 : ℝ) (71 / 800 : ℝ) ≤ (4177016213 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (71 / 400 : ℝ)) (1875889253708197 / 500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (71 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell141_product_upper
  have hD : (202786445643 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (141 / 800 : ℝ) - (71 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell141_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell141_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (141 / 800 : ℝ) - (71 / 1600 : ℝ)) ≤
      (1 / (202786445643 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (202786445643 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((71 / 1600 : ℝ) - Real.pi * Real.exp (141 / 800 : ℝ)) ≤
      (2 / (202786445643 / 5000000000 : ℝ) : ℝ) := by
    rw [show (71 / 1600 : ℝ) - Real.pi * Real.exp (141 / 800 : ℝ) =
      -(Real.pi * Real.exp (141 / 800 : ℝ) - (71 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1875889253708197 / 500000000000000 : ℝ) ^ 2 - 6 *
      (1875889253708197 / 500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell141_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (141 / 1600 : ℝ) (71 / 800 : ℝ)) :
    (1032866411 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4177016213 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell141_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell141_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell142_leftExp :
    (5971140289 / 5000000000 : ℝ) ≤ Real.exp (71 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (71 / 400 : ℝ) (502781143697 / 500000000000 : ℝ)
    (5971140289 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell142_rightExp :
    Real.exp (143 / 800 : ℝ) ≤ (2989304441 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (143 / 800 : ℝ) (1005601567939 / 1000000000000 : ℝ)
    (2989304441 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell142_denomUpper :
    Real.exp (9280240406714513 / 2500000000000000 : ℝ) ≤ (409395325693 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9280240406714513 / 2500000000000000 : ℝ) (280749811709 /
    250000000000 : ℝ) (409395325693 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell142_denomLower :
    (407350871229 / 10000000000 : ℝ) ≤ Real.exp (2316931132850011 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2316931132850011 / 625000000000000 : ℝ) (224564713819 /
    200000000000 : ℝ) (407350871229 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell142_product_lower :
    (2344860820350011 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (71 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell142_leftExp
    (by norm_num : (0 : ℝ) ≤ (5971140289 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell142_product_upper :
    Real.pi * Real.exp (143 / 800 : ℝ) ≤ (9391177906714513 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell142_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell142_endpointLower :
    (825428773 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (71 / 800 : ℝ) (143 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2344860820350011 / 625000000000000 : ℝ) (Real.pi * Real.exp (71 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell142_product_lower
  have hD : Real.exp (Real.pi * Real.exp (143 / 800 : ℝ) - (71 / 1600 : ℝ)) ≤
      (409395325693 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell142_denomUpper
    linarith [hpThetaJensenCell142_product_upper]
  have hi : (1 / (409395325693 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (143 / 800 : ℝ) - (71 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (409395325693 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (409395325693 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((71 / 1600 : ℝ) - Real.pi * Real.exp (143 / 800 : ℝ)) := by
    rw [show (71 / 1600 : ℝ) - Real.pi * Real.exp (143 / 800 : ℝ) =
      -(Real.pi * Real.exp (143 / 800 : ℝ) - (71 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (71 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (71 / 400 : ℝ)) := by
    have h := hpThetaJensenCell142_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (409395325693 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell142_endpointUpper :
    hpThetaJensenKernelEndpointUpper (71 / 800 : ℝ) (143 / 1600 : ℝ) ≤ (16690656057 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (143 / 800 : ℝ)) (9391177906714513 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (143 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell142_product_upper
  have hD : (407350871229 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (71 / 400 : ℝ) - (143 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell142_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell142_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (71 / 400 : ℝ) - (143 / 3200 : ℝ)) ≤
      (1 / (407350871229 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (407350871229 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((143 / 3200 : ℝ) - Real.pi * Real.exp (71 / 400 : ℝ)) ≤
      (2 / (407350871229 / 10000000000 : ℝ) : ℝ) := by
    rw [show (143 / 3200 : ℝ) - Real.pi * Real.exp (71 / 400 : ℝ) =
      -(Real.pi * Real.exp (71 / 400 : ℝ) - (143 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9391177906714513 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (9391177906714513 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell142_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (71 / 800 : ℝ) (143 / 1600 : ℝ)) :
    (825428773 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (16690656057 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell142_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell142_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell143_leftExp :
    (11957217763 / 10000000000 : ℝ) ≤ Real.exp (143 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (143 / 800 : ℝ) (502800783969 / 500000000000 : ℝ)
    (11957217763 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell143_rightExp :
    Real.exp (9 / 50 : ℝ) ≤ (187065213 / 156250000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9 / 50 : ℝ) (502820425009 / 500000000000 : ℝ)
    (187065213 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell143_denomUpper :
    Real.exp (580700341829309 / 156250000000000 : ℝ) ≤ (411194887407 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (580700341829309 / 156250000000000 : ℝ) (1123153179347 /
    1000000000000 : ℝ) (411194887407 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell143_denomLower :
    (409139044193 / 10000000000 : ℝ) ≤ Real.exp (4639337458312337 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4639337458312337 / 1250000000000000 : ℝ) (1122977271497
    / 1000000000000 : ℝ) (409139044193 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell143_product_lower :
    (4695587458312337 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (143 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell143_leftExp
    (by norm_num : (0 : ℝ) ≤ (11957217763 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell143_product_upper :
    Real.pi * Real.exp (9 / 50 : ℝ) ≤ (587682763704309 / 156250000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell143_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell143_endpointLower :
    (16491181033 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (143 / 1600 : ℝ) (9 / 100 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4695587458312337 / 1250000000000000 : ℝ) (Real.pi * Real.exp (143 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell143_product_lower
  have hD : Real.exp (Real.pi * Real.exp (9 / 50 : ℝ) - (143 / 3200 : ℝ)) ≤
      (411194887407 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell143_denomUpper
    linarith [hpThetaJensenCell143_product_upper]
  have hi : (1 / (411194887407 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (9 / 50 : ℝ) - (143 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (411194887407 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (411194887407 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((143 / 3200 : ℝ) - Real.pi * Real.exp (9 / 50 : ℝ)) := by
    rw [show (143 / 3200 : ℝ) - Real.pi * Real.exp (9 / 50 : ℝ) =
      -(Real.pi * Real.exp (9 / 50 : ℝ) - (143 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (143 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (143 / 800 : ℝ)) := by
    have h := hpThetaJensenCell143_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (411194887407 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell143_endpointUpper :
    hpThetaJensenKernelEndpointUpper (143 / 1600 : ℝ) (9 / 100 : ℝ) ≤ (4168284707 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (9 / 50 : ℝ)) (587682763704309 / 156250000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (9 / 100 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell143_product_upper
  have hD : (409139044193 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (143 / 800 : ℝ) - (9 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell143_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell143_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (143 / 800 : ℝ) - (9 / 200 : ℝ)) ≤
      (1 / (409139044193 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (409139044193 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((9 / 200 : ℝ) - Real.pi * Real.exp (143 / 800 : ℝ)) ≤
      (2 / (409139044193 / 10000000000 : ℝ) : ℝ) := by
    rw [show (9 / 200 : ℝ) - Real.pi * Real.exp (143 / 800 : ℝ) =
      -(Real.pi * Real.exp (143 / 800 : ℝ) - (9 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (587682763704309 / 156250000000000 : ℝ) ^ 2 - 6 *
      (587682763704309 / 156250000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell143_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (143 / 1600 : ℝ) (9 / 100 : ℝ)) :
    (16491181033 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4168284707 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell143_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell143_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell144_leftExp :
    (11972173631 / 10000000000 : ℝ) ≤ Real.exp (9 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9 / 50 : ℝ) (1005640850017 / 1000000000000 : ℝ)
    (11972173631 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell144_rightExp :
    Real.exp (29 / 160 : ℝ) ≤ (5993574103 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (29 / 160 : ℝ) (1005680133631 / 1000000000000 : ℝ)
    (5993574103 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell144_denomUpper :
    Real.exp (18604370446966079 / 5000000000000000 : ℝ) ≤ (413004786467 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (18604370446966079 / 5000000000000000 : ℝ) (1123307339249
    / 1000000000000 : ℝ) (413004786467 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell144_denomLower :
    (16437499151 / 400000000 : ℝ) ≤ Real.exp (4644819987720069 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4644819987720069 / 1250000000000000 : ℝ) (70195700059 /
    62500000000 : ℝ) (16437499151 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell144_product_lower :
    (4701460612720069 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (9 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell144_leftExp
    (by norm_num : (0 : ℝ) ≤ (11972173631 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell144_product_upper :
    Real.pi * Real.exp (29 / 160 : ℝ) ≤ (18829370446966079 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell144_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell144_endpointLower :
    (16473679637 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (9 / 100 : ℝ) (29 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4701460612720069 / 1250000000000000 : ℝ) (Real.pi * Real.exp (9 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell144_product_lower
  have hD : Real.exp (Real.pi * Real.exp (29 / 160 : ℝ) - (9 / 200 : ℝ)) ≤
      (413004786467 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell144_denomUpper
    linarith [hpThetaJensenCell144_product_upper]
  have hi : (1 / (413004786467 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (29 / 160 : ℝ) - (9 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (413004786467 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (413004786467 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((9 / 200 : ℝ) - Real.pi * Real.exp (29 / 160 : ℝ)) := by
    rw [show (9 / 200 : ℝ) - Real.pi * Real.exp (29 / 160 : ℝ) =
      -(Real.pi * Real.exp (29 / 160 : ℝ) - (9 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (9 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (9 / 50 : ℝ)) := by
    have h := hpThetaJensenCell144_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (413004786467 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell144_endpointUpper :
    hpThetaJensenKernelEndpointUpper (9 / 100 : ℝ) (29 / 320 : ℝ) ≤ (3331102701 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (29 / 160 : ℝ)) (18829370446966079 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (29 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell144_product_upper
  have hD : (16437499151 / 400000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (9 / 50 : ℝ) - (29 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell144_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell144_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (9 / 50 : ℝ) - (29 / 640 : ℝ)) ≤
      (1 / (16437499151 / 400000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (16437499151 / 400000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((29 / 640 : ℝ) - Real.pi * Real.exp (9 / 50 : ℝ)) ≤
      (2 / (16437499151 / 400000000 : ℝ) : ℝ) := by
    rw [show (29 / 640 : ℝ) - Real.pi * Real.exp (9 / 50 : ℝ) =
      -(Real.pi * Real.exp (9 / 50 : ℝ) - (29 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (18829370446966079 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (18829370446966079 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell144_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (9 / 100 : ℝ) (29 / 320 : ℝ)) :
    (16473679637 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3331102701 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell144_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell144_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell145_leftExp :
    (2397429641 / 2000000000 : ℝ) ≤ Real.exp (29 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (29 / 160 : ℝ) (100568013363 / 100000000000 : ℝ)
    (2397429641 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell145_rightExp :
    Real.exp (73 / 400 : ℝ) ≤ (1200214151 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (73 / 400 : ℝ) (502859709389 / 500000000000 : ℝ)
    (1200214151 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell145_denomUpper :
    Real.exp (3725271875282543 / 1000000000000000 : ℝ) ≤ (82965018563 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3725271875282543 / 1000000000000000 : ℝ) (561730863447 /
    500000000000 : ℝ) (82965018563 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell145_denomLower :
    (20637312211 / 500000000 : ℝ) ≤ Real.exp (930061972591059 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (930061972591059 / 250000000000000 : ℝ) (1123285357777 /
    1000000000000 : ℝ) (20637312211 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell145_product_lower :
    (941468222591059 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (29 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell145_leftExp
    (by norm_num : (0 : ℝ) ≤ (2397429641 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell145_product_upper :
    Real.pi * Real.exp (73 / 400 : ℝ) ≤ (3770584375282543 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell145_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell145_endpointLower :
    (16456071609 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (29 / 320 : ℝ) (73 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (941468222591059 / 250000000000000 : ℝ) (Real.pi * Real.exp (29 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell145_product_lower
  have hD : Real.exp (Real.pi * Real.exp (73 / 400 : ℝ) - (29 / 640 : ℝ)) ≤
      (82965018563 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell145_denomUpper
    linarith [hpThetaJensenCell145_product_upper]
  have hi : (1 / (82965018563 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (73 / 400 : ℝ) - (29 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (82965018563 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (82965018563 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((29 / 640 : ℝ) - Real.pi * Real.exp (73 / 400 : ℝ)) := by
    rw [show (29 / 640 : ℝ) - Real.pi * Real.exp (73 / 400 : ℝ) =
      -(Real.pi * Real.exp (73 / 400 : ℝ) - (29 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (29 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (29 / 160 : ℝ)) := by
    have h := hpThetaJensenCell145_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (82965018563 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell145_endpointUpper :
    hpThetaJensenKernelEndpointUpper (29 / 320 : ℝ) (73 / 800 : ℝ) ≤ (8318890219 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (73 / 400 : ℝ)) (3770584375282543 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (73 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell145_product_upper
  have hD : (20637312211 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (29 / 160 : ℝ) - (73 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell145_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell145_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (29 / 160 : ℝ) - (73 / 1600 : ℝ)) ≤
      (1 / (20637312211 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (20637312211 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((73 / 1600 : ℝ) - Real.pi * Real.exp (29 / 160 : ℝ)) ≤
      (2 / (20637312211 / 500000000 : ℝ) : ℝ) := by
    rw [show (73 / 1600 : ℝ) - Real.pi * Real.exp (29 / 160 : ℝ) =
      -(Real.pi * Real.exp (29 / 160 : ℝ) - (73 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (3770584375282543 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (3770584375282543 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell145_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (29 / 320 : ℝ) (73 / 800 : ℝ)) :
    (16456071609 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8318890219 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell145_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell145_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell146_leftExp :
    (12002141509 / 10000000000 : ℝ) ≤ Real.exp (73 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (73 / 400 : ℝ) (1005719418777 / 1000000000000 : ℝ)
    (12002141509 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell146_rightExp :
    Real.exp (147 / 800 : ℝ) ≤ (375536049 / 312500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (147 / 800 : ℝ) (50287935273 / 50000000000 : ℝ)
    (375536049 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell146_denomUpper :
    Real.exp (1165523610286057 / 312500000000000 : ℝ) ≤ (416655876931 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1165523610286057 / 312500000000000 : ℝ) (224723268527 /
    200000000000 : ℝ) (416655876931 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell146_denomLower :
    (207282705213 / 5000000000 : ℝ) ≤ Real.exp (4655807093442791 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4655807093442791 / 1250000000000000 : ℝ) (280859935587 /
    250000000000 : ℝ) (207282705213 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell146_product_lower :
    (4713228968442791 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (73 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell146_leftExp
    (by norm_num : (0 : ℝ) ≤ (12002141509 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell146_product_upper :
    Real.pi * Real.exp (147 / 800 : ℝ) ≤ (1179781422786057 / 312500000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell146_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell146_endpointLower :
    (16438357291 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (73 / 800 : ℝ) (147 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4713228968442791 / 1250000000000000 : ℝ) (Real.pi * Real.exp (73 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell146_product_lower
  have hD : Real.exp (Real.pi * Real.exp (147 / 800 : ℝ) - (73 / 1600 : ℝ)) ≤
      (416655876931 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell146_denomUpper
    linarith [hpThetaJensenCell146_product_upper]
  have hi : (1 / (416655876931 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (147 / 800 : ℝ) - (73 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (416655876931 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (416655876931 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((73 / 1600 : ℝ) - Real.pi * Real.exp (147 / 800 : ℝ)) := by
    rw [show (73 / 1600 : ℝ) - Real.pi * Real.exp (147 / 800 : ℝ) =
      -(Real.pi * Real.exp (147 / 800 : ℝ) - (73 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (73 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (73 / 400 : ℝ)) := by
    have h := hpThetaJensenCell146_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (416655876931 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell146_endpointUpper :
    hpThetaJensenKernelEndpointUpper (73 / 800 : ℝ) (147 / 1600 : ℝ) ≤ (16619939969 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (147 / 800 : ℝ)) (1179781422786057 / 312500000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (147 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell146_product_upper
  have hD : (207282705213 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (73 / 400 : ℝ) - (147 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell146_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell146_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (73 / 400 : ℝ) - (147 / 3200 : ℝ)) ≤
      (1 / (207282705213 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (207282705213 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((147 / 3200 : ℝ) - Real.pi * Real.exp (73 / 400 : ℝ)) ≤
      (2 / (207282705213 / 5000000000 : ℝ) : ℝ) := by
    rw [show (147 / 3200 : ℝ) - Real.pi * Real.exp (73 / 400 : ℝ) =
      -(Real.pi * Real.exp (73 / 400 : ℝ) - (147 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1179781422786057 / 312500000000000 : ℝ) ^ 2 - 6 *
      (1179781422786057 / 312500000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell146_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (73 / 800 : ℝ) (147 / 1600 : ℝ)) :
    (16438357291 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (16619939969 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell146_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell146_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell147_leftExp :
    (6008576783 / 5000000000 : ℝ) ≤ Real.exp (147 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (147 / 800 : ℝ) (1005758705459 / 1000000000000 : ℝ)
    (6008576783 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell147_rightExp :
    Real.exp (37 / 200 : ℝ) ≤ (6016092201 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (37 / 200 : ℝ) (1005797993677 / 1000000000000 : ℝ)
    (6016092201 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell147_denomUpper :
    Real.exp (18670425646016193 / 5000000000000000 : ℝ) ≤ (418497209573 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (18670425646016193 / 5000000000000000 : ℝ) (1123771186803
    / 1000000000000 : ℝ) (418497209573 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell147_denomLower :
    (4163950477 / 100000000 : ℝ) ≤ Real.exp (2330655844107317 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2330655844107317 / 625000000000000 : ℝ) (1123594354999 /
    1000000000000 : ℝ) (4163950477 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell147_product_lower :
    (2359562094107317 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (147 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell147_leftExp
    (by norm_num : (0 : ℝ) ≤ (6008576783 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell147_product_upper :
    Real.pi * Real.exp (37 / 200 : ℝ) ≤ (18900113146016193 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell147_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell147_endpointLower :
    (8210268517 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (147 / 1600 : ℝ) (37 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2359562094107317 / 625000000000000 : ℝ) (Real.pi * Real.exp (147 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell147_product_lower
  have hD : Real.exp (Real.pi * Real.exp (37 / 200 : ℝ) - (147 / 3200 : ℝ)) ≤
      (418497209573 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell147_denomUpper
    linarith [hpThetaJensenCell147_product_upper]
  have hi : (1 / (418497209573 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (37 / 200 : ℝ) - (147 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (418497209573 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (418497209573 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((147 / 3200 : ℝ) - Real.pi * Real.exp (37 / 200 : ℝ)) := by
    rw [show (147 / 3200 : ℝ) - Real.pi * Real.exp (37 / 200 : ℝ) =
      -(Real.pi * Real.exp (37 / 200 : ℝ) - (147 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (147 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (147 / 800 : ℝ)) := by
    have h := hpThetaJensenCell147_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (418497209573 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell147_endpointUpper :
    hpThetaJensenKernelEndpointUpper (147 / 1600 : ℝ) (37 / 400 : ℝ) ≤ (8300996221 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (37 / 200 : ℝ)) (18900113146016193 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (37 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell147_product_upper
  have hD : (4163950477 / 100000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (147 / 800 : ℝ) - (37 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell147_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell147_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (147 / 800 : ℝ) - (37 / 800 : ℝ)) ≤
      (1 / (4163950477 / 100000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4163950477 / 100000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((37 / 800 : ℝ) - Real.pi * Real.exp (147 / 800 : ℝ)) ≤
      (2 / (4163950477 / 100000000 : ℝ) : ℝ) := by
    rw [show (37 / 800 : ℝ) - Real.pi * Real.exp (147 / 800 : ℝ) =
      -(Real.pi * Real.exp (147 / 800 : ℝ) - (37 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (18900113146016193 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (18900113146016193 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell147_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (147 / 1600 : ℝ) (37 / 400 : ℝ)) :
    (8210268517 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8300996221 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell147_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell147_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell148_leftExp :
    (12032184401 / 10000000000 : ℝ) ≤ Real.exp (37 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (37 / 200 : ℝ) (251449498419 / 250000000000 : ℝ)
    (12032184401 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell148_rightExp :
    Real.exp (149 / 800 : ℝ) ≤ (12047234037 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (149 / 800 : ℝ) (1005837283429 / 1000000000000 : ℝ)
    (12047234037 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell148_denomUpper :
    Real.exp (37385006120000941 / 10000000000000000 : ℝ) ≤ (420349162423 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (37385006120000941 / 10000000000000000 : ℝ) (561963129881
    / 500000000000 : ℝ) (420349162423 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell148_denomLower :
    (104558806789 / 2500000000 : ℝ) ≤ Real.exp (4666823657088299 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4666823657088299 / 1250000000000000 : ℝ) (224749839219 /
    200000000000 : ℝ) (104558806789 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell148_product_lower :
    (4725026782088299 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (37 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell148_leftExp
    (by norm_num : (0 : ℝ) ≤ (12032184401 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell148_product_upper :
    Real.pi * Real.exp (149 / 800 : ℝ) ≤ (37847506120000941 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell148_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell148_endpointLower :
    (8201305591 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (37 / 400 : ℝ) (149 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4725026782088299 / 1250000000000000 : ℝ) (Real.pi * Real.exp (37 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell148_product_lower
  have hD : Real.exp (Real.pi * Real.exp (149 / 800 : ℝ) - (37 / 800 : ℝ)) ≤
      (420349162423 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell148_denomUpper
    linarith [hpThetaJensenCell148_product_upper]
  have hi : (1 / (420349162423 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (149 / 800 : ℝ) - (37 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (420349162423 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (420349162423 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((37 / 800 : ℝ) - Real.pi * Real.exp (149 / 800 : ℝ)) := by
    rw [show (37 / 800 : ℝ) - Real.pi * Real.exp (149 / 800 : ℝ) =
      -(Real.pi * Real.exp (149 / 800 : ℝ) - (37 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (37 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (37 / 200 : ℝ)) := by
    have h := hpThetaJensenCell148_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (420349162423 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell148_endpointUpper :
    hpThetaJensenKernelEndpointUpper (37 / 400 : ℝ) (149 / 1600 : ℝ) ≤ (8291969101 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (149 / 800 : ℝ)) (37847506120000941 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (149 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell148_product_upper
  have hD : (104558806789 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (37 / 200 : ℝ) - (149 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell148_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell148_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (37 / 200 : ℝ) - (149 / 3200 : ℝ)) ≤
      (1 / (104558806789 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (104558806789 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((149 / 3200 : ℝ) - Real.pi * Real.exp (37 / 200 : ℝ)) ≤
      (2 / (104558806789 / 2500000000 : ℝ) : ℝ) := by
    rw [show (149 / 3200 : ℝ) - Real.pi * Real.exp (37 / 200 : ℝ) =
      -(Real.pi * Real.exp (37 / 200 : ℝ) - (149 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (37847506120000941 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (37847506120000941 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell148_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (37 / 400 : ℝ) (149 / 1600 : ℝ)) :
    (8201305591 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8291969101 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell148_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell148_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell149_leftExp :
    (2409446807 / 2000000000 : ℝ) ≤ Real.exp (149 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (149 / 800 : ℝ) (251459320857 / 250000000000 : ℝ)
    (2409446807 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell149_rightExp :
    Real.exp (3 / 16 : ℝ) ≤ (2412460499 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3 / 16 : ℝ) (201175314943 / 200000000000 : ℝ)
    (2412460499 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell149_denomUpper :
    Real.exp (7485844016434907 / 2000000000000000 : ℝ) ≤ (13194118979 / 312500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7485844016434907 / 2000000000000000 : ℝ) (281020390461 /
    250000000000 : ℝ) (13194118979 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell149_denomLower :
    (420086019911 / 10000000000 : ℝ) ≤ Real.exp (934468601662093 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (934468601662093 / 250000000000000 : ℝ) (280976066489 /
    250000000000 : ℝ) (420086019911 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell149_product_lower :
    (946187351662093 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (149 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell149_leftExp
    (by norm_num : (0 : ℝ) ≤ (2409446807 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell149_product_upper :
    Real.pi * Real.exp (3 / 16 : ℝ) ≤ (7578969016434907 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell149_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell149_endpointLower :
    (8192290041 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (149 / 1600 : ℝ) (3 / 32 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (946187351662093 / 250000000000000 : ℝ) (Real.pi * Real.exp (149 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell149_product_lower
  have hD : Real.exp (Real.pi * Real.exp (3 / 16 : ℝ) - (149 / 3200 : ℝ)) ≤
      (13194118979 / 312500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell149_denomUpper
    linarith [hpThetaJensenCell149_product_upper]
  have hi : (1 / (13194118979 / 312500000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (3 / 16 : ℝ) - (149 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (13194118979 / 312500000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (13194118979 / 312500000 : ℝ) : ℝ) ≤
      2 * Real.exp ((149 / 3200 : ℝ) - Real.pi * Real.exp (3 / 16 : ℝ)) := by
    rw [show (149 / 3200 : ℝ) - Real.pi * Real.exp (3 / 16 : ℝ) =
      -(Real.pi * Real.exp (3 / 16 : ℝ) - (149 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (149 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (149 / 800 : ℝ)) := by
    have h := hpThetaJensenCell149_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (13194118979 / 312500000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell149_endpointUpper :
    hpThetaJensenKernelEndpointUpper (149 / 1600 : ℝ) (3 / 32 : ℝ) ≤ (8282888803 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (3 / 16 : ℝ)) (7578969016434907 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (3 / 32 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell149_product_upper
  have hD : (420086019911 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (149 / 800 : ℝ) - (3 / 64 : ℝ)) := by
    apply le_trans hpThetaJensenCell149_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell149_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (149 / 800 : ℝ) - (3 / 64 : ℝ)) ≤
      (1 / (420086019911 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (420086019911 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((3 / 64 : ℝ) - Real.pi * Real.exp (149 / 800 : ℝ)) ≤
      (2 / (420086019911 / 10000000000 : ℝ) : ℝ) := by
    rw [show (3 / 64 : ℝ) - Real.pi * Real.exp (149 / 800 : ℝ) =
      -(Real.pi * Real.exp (149 / 800 : ℝ) - (3 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (7578969016434907 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (7578969016434907 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell149_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (149 / 1600 : ℝ) (3 / 32 : ℝ)) :
    (8192290041 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8282888803 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell149_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell149_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell150_leftExp :
    (6031151247 / 5000000000 : ℝ) ≤ Real.exp (3 / 16 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3 / 16 : ℝ) (502938287357 / 500000000000 : ℝ)
    (6031151247 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell150_rightExp :
    Real.exp (151 / 800 : ℝ) ≤ (12077389801 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (151 / 800 : ℝ) (62869741721 / 62500000000 : ℝ)
    (12077389801 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell150_denomUpper :
    Real.exp (37473493257092993 / 10000000000000000 : ℝ) ≤ (16963408683 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (37473493257092993 / 10000000000000000 : ℝ) (562118546707
    / 500000000000 : ℝ) (16963408683 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell150_denomLower :
    (105486874573 / 2500000000 : ℝ) ≤ Real.exp (2338934876045653 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2338934876045653 / 625000000000000 : ℝ) (562029782479 /
    500000000000 : ℝ) (105486874573 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell150_product_lower :
    (2368427063545653 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (3 / 16 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell150_leftExp
    (by norm_num : (0 : ℝ) ≤ (6031151247 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell150_product_upper :
    Real.pi * Real.exp (151 / 800 : ℝ) ≤ (37942243257092993 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell150_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell150_endpointLower :
    (3273288817 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (3 / 32 : ℝ) (151 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2368427063545653 / 625000000000000 : ℝ) (Real.pi * Real.exp (3 / 16 : ℝ))
    (by norm_num) hpThetaJensenCell150_product_lower
  have hD : Real.exp (Real.pi * Real.exp (151 / 800 : ℝ) - (3 / 64 : ℝ)) ≤
      (16963408683 / 400000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell150_denomUpper
    linarith [hpThetaJensenCell150_product_upper]
  have hi : (1 / (16963408683 / 400000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (151 / 800 : ℝ) - (3 / 64 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (16963408683 / 400000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (16963408683 / 400000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((3 / 64 : ℝ) - Real.pi * Real.exp (151 / 800 : ℝ)) := by
    rw [show (3 / 64 : ℝ) - Real.pi * Real.exp (151 / 800 : ℝ) =
      -(Real.pi * Real.exp (151 / 800 : ℝ) - (3 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (3 / 16 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (3 / 16 : ℝ)) := by
    have h := hpThetaJensenCell150_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (16963408683 / 400000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell150_endpointUpper :
    hpThetaJensenKernelEndpointUpper (3 / 32 : ℝ) (151 / 1600 : ℝ) ≤ (8273755499 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (151 / 800 : ℝ)) (37942243257092993 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (151 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell150_product_upper
  have hD : (105486874573 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (3 / 16 : ℝ) - (151 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell150_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell150_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (3 / 16 : ℝ) - (151 / 3200 : ℝ)) ≤
      (1 / (105486874573 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (105486874573 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((151 / 3200 : ℝ) - Real.pi * Real.exp (3 / 16 : ℝ)) ≤
      (2 / (105486874573 / 2500000000 : ℝ) : ℝ) := by
    rw [show (151 / 3200 : ℝ) - Real.pi * Real.exp (3 / 16 : ℝ) =
      -(Real.pi * Real.exp (3 / 16 : ℝ) - (151 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (37942243257092993 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (37942243257092993 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell150_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (3 / 32 : ℝ) (151 / 1600 : ℝ)) :
    (3273288817 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8273755499 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell150_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell150_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell151_leftExp :
    (12077389799 / 10000000000 : ℝ) ≤ Real.exp (151 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (151 / 800 : ℝ) (201183173507 / 200000000000 : ℝ)
    (12077389799 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell151_rightExp :
    Real.exp (19 / 100 : ℝ) ≤ (12092495977 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (19 / 100 : ℝ) (251488790473 / 250000000000 : ℝ)
    (12092495977 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell151_denomUpper :
    Real.exp (37517825713871361 / 10000000000000000 : ℝ) ≤ (425969464619 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (37517825713871361 / 10000000000000000 : ℝ) (224878570961
    / 200000000000 : ℝ) (425969464619 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell151_denomLower :
    (423819734487 / 10000000000 : ℝ) ≤ Real.exp (4683403896677501 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4683403896677501 / 1250000000000000 : ℝ) (56210754671 /
    50000000000 : ℝ) (423819734487 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell151_product_lower :
    (4742778896677501 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (151 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell151_leftExp
    (by norm_num : (0 : ℝ) ≤ (12077389799 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell151_product_upper :
    Real.pi * Real.exp (19 / 100 : ℝ) ≤ (37989700713871361 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell151_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell151_endpointLower :
    (8174101771 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (151 / 1600 : ℝ) (19 / 200 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4742778896677501 / 1250000000000000 : ℝ) (Real.pi * Real.exp (151 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell151_product_lower
  have hD : Real.exp (Real.pi * Real.exp (19 / 100 : ℝ) - (151 / 3200 : ℝ)) ≤
      (425969464619 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell151_denomUpper
    linarith [hpThetaJensenCell151_product_upper]
  have hi : (1 / (425969464619 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (19 / 100 : ℝ) - (151 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (425969464619 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (425969464619 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((151 / 3200 : ℝ) - Real.pi * Real.exp (19 / 100 : ℝ)) := by
    rw [show (151 / 3200 : ℝ) - Real.pi * Real.exp (19 / 100 : ℝ) =
      -(Real.pi * Real.exp (19 / 100 : ℝ) - (151 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (151 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (151 / 800 : ℝ)) := by
    have h := hpThetaJensenCell151_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (425969464619 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell151_endpointUpper :
    hpThetaJensenKernelEndpointUpper (151 / 1600 : ℝ) (19 / 200 : ℝ) ≤ (16529138739 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (19 / 100 : ℝ)) (37989700713871361 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (19 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell151_product_upper
  have hD : (423819734487 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (151 / 800 : ℝ) - (19 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell151_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell151_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (151 / 800 : ℝ) - (19 / 400 : ℝ)) ≤
      (1 / (423819734487 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (423819734487 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((19 / 400 : ℝ) - Real.pi * Real.exp (151 / 800 : ℝ)) ≤
      (2 / (423819734487 / 10000000000 : ℝ) : ℝ) := by
    rw [show (19 / 400 : ℝ) - Real.pi * Real.exp (151 / 800 : ℝ) =
      -(Real.pi * Real.exp (151 / 800 : ℝ) - (19 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (37989700713871361 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (37989700713871361 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell151_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (151 / 1600 : ℝ) (19 / 200 : ℝ)) :
    (8174101771 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (16529138739 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell151_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell151_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell152_leftExp :
    (1511561997 / 1250000000 : ℝ) ≤ Real.exp (19 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (19 / 100 : ℝ) (1005955161891 / 1000000000000 : ℝ)
    (1511561997 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell152_rightExp :
    Real.exp (153 / 800 : ℝ) ≤ (1513452631 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (153 / 800 : ℝ) (1005994457783 / 1000000000000 : ℝ)
    (1513452631 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell152_denomUpper :
    Real.exp (4695277191381183 / 1250000000000000 : ℝ) ≤ (427864623843 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4695277191381183 / 1250000000000000 : ℝ) (1124548846381
    / 1000000000000 : ℝ) (427864623843 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell152_denomLower :
    (106425700487 / 2500000000 : ℝ) ≤ Real.exp (586118181534903 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (586118181534903 / 156250000000000 : ℝ) (28109271293 /
    25000000000 : ℝ) (106425700487 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell152_product_lower :
    (593588884659903 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (19 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell152_leftExp
    (by norm_num : (0 : ℝ) ≤ (1511561997 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell152_product_upper :
    Real.pi * Real.exp (153 / 800 : ℝ) ≤ (4754652191381183 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell152_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell152_endpointLower :
    (2041232351 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (19 / 200 : ℝ) (153 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (593588884659903 / 156250000000000 : ℝ) (Real.pi * Real.exp (19 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell152_product_lower
  have hD : Real.exp (Real.pi * Real.exp (153 / 800 : ℝ) - (19 / 400 : ℝ)) ≤
      (427864623843 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell152_denomUpper
    linarith [hpThetaJensenCell152_product_upper]
  have hi : (1 / (427864623843 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (153 / 800 : ℝ) - (19 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (427864623843 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (427864623843 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((19 / 400 : ℝ) - Real.pi * Real.exp (153 / 800 : ℝ)) := by
    rw [show (19 / 400 : ℝ) - Real.pi * Real.exp (153 / 800 : ℝ) =
      -(Real.pi * Real.exp (153 / 800 : ℝ) - (19 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (19 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (19 / 100 : ℝ)) := by
    have h := hpThetaJensenCell152_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (427864623843 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell152_endpointUpper :
    hpThetaJensenKernelEndpointUpper (19 / 200 : ℝ) (153 / 1600 : ℝ) ≤ (2063832647 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (153 / 800 : ℝ)) (4754652191381183 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (153 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell152_product_upper
  have hD : (106425700487 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (19 / 100 : ℝ) - (153 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell152_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell152_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (19 / 100 : ℝ) - (153 / 3200 : ℝ)) ≤
      (1 / (106425700487 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (106425700487 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((153 / 3200 : ℝ) - Real.pi * Real.exp (19 / 100 : ℝ)) ≤
      (2 / (106425700487 / 2500000000 : ℝ) : ℝ) := by
    rw [show (153 / 3200 : ℝ) - Real.pi * Real.exp (19 / 100 : ℝ) =
      -(Real.pi * Real.exp (19 / 100 : ℝ) - (153 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4754652191381183 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (4754652191381183 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell152_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (19 / 200 : ℝ) (153 / 1600 : ℝ)) :
    (2041232351 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2063832647 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell152_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell152_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell153_leftExp :
    (12107621047 / 10000000000 : ℝ) ≤ Real.exp (153 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (153 / 800 : ℝ) (502997228891 / 500000000000 : ℝ)
    (12107621047 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell153_rightExp :
    Real.exp (77 / 400 : ℝ) ≤ (6061382519 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (77 / 400 : ℝ) (1006033755209 / 1000000000000 : ℝ)
    (6061382519 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell153_denomUpper :
    Real.exp (18803334392012767 / 5000000000000000 : ℝ) ≤ (6715168267 / 156250000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (18803334392012767 / 5000000000000000 : ℝ) (1124705068497
    / 1000000000000 : ℝ) (6715168267 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell153_denomLower :
    (21379838707 / 500000000 : ℝ) ≤ Real.exp (4694494427535853 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4694494427535853 / 1250000000000000 : ℝ) (1124526840191
    / 1000000000000 : ℝ) (21379838707 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell153_product_lower :
    (4754650677535853 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (153 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell153_leftExp
    (by norm_num : (0 : ℝ) ≤ (12107621047 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell153_product_upper :
    Real.pi * Real.exp (77 / 400 : ℝ) ≤ (19042396892012767 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell153_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell153_endpointLower :
    (16311410229 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (153 / 1600 : ℝ) (77 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4754650677535853 / 1250000000000000 : ℝ) (Real.pi * Real.exp (153 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell153_product_lower
  have hD : Real.exp (Real.pi * Real.exp (77 / 400 : ℝ) - (153 / 3200 : ℝ)) ≤
      (6715168267 / 156250000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell153_denomUpper
    linarith [hpThetaJensenCell153_product_upper]
  have hi : (1 / (6715168267 / 156250000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (77 / 400 : ℝ) - (153 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (6715168267 / 156250000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (6715168267 / 156250000 : ℝ) : ℝ) ≤
      2 * Real.exp ((153 / 3200 : ℝ) - Real.pi * Real.exp (77 / 400 : ℝ)) := by
    rw [show (153 / 3200 : ℝ) - Real.pi * Real.exp (77 / 400 : ℝ) =
      -(Real.pi * Real.exp (77 / 400 : ℝ) - (153 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (153 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (153 / 800 : ℝ)) := by
    have h := hpThetaJensenCell153_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (6715168267 / 156250000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell153_endpointUpper :
    hpThetaJensenKernelEndpointUpper (153 / 1600 : ℝ) (77 / 800 : ℝ) ≤ (659683147 / 400000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (77 / 400 : ℝ)) (19042396892012767 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (77 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell153_product_upper
  have hD : (21379838707 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (153 / 800 : ℝ) - (77 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell153_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell153_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (153 / 800 : ℝ) - (77 / 1600 : ℝ)) ≤
      (1 / (21379838707 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (21379838707 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((77 / 1600 : ℝ) - Real.pi * Real.exp (153 / 800 : ℝ)) ≤
      (2 / (21379838707 / 500000000 : ℝ) : ℝ) := by
    rw [show (77 / 1600 : ℝ) - Real.pi * Real.exp (153 / 800 : ℝ) =
      -(Real.pi * Real.exp (153 / 800 : ℝ) - (77 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (19042396892012767 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (19042396892012767 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell153_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (153 / 1600 : ℝ) (77 / 800 : ℝ)) :
    (16311410229 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (659683147 / 400000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell153_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell153_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell154_leftExp :
    (3030691259 / 2500000000 : ℝ) ≤ Real.exp (77 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (77 / 400 : ℝ) (125754219401 / 125000000000 : ℝ)
    (3030691259 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell154_rightExp :
    Real.exp (31 / 160 : ℝ) ≤ (12137927969 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (31 / 160 : ℝ) (100607305417 / 100000000000 : ℝ)
    (12137927969 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell154_denomUpper :
    Real.exp (37651179541914617 / 10000000000000000 : ℝ) ≤ (431687975013 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (37651179541914617 / 10000000000000000 : ℝ) (70303845093
    / 62500000000 : ℝ) (431687975013 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell154_denomLower :
    (26843857833 / 625000000 : ℝ) ≤ Real.exp (1175012707968041 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1175012707968041 / 312500000000000 : ℝ) (562341529593 /
    500000000000 : ℝ) (26843857833 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell154_product_lower :
    (1190149426718041 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (77 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell154_leftExp
    (by norm_num : (0 : ℝ) ≤ (3030691259 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell154_product_upper :
    Real.pi * Real.exp (31 / 160 : ℝ) ≤ (38132429541914617 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell154_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell154_endpointLower :
    (16292858171 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (77 / 800 : ℝ) (31 / 320 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1190149426718041 / 312500000000000 : ℝ) (Real.pi * Real.exp (77 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell154_product_lower
  have hD : Real.exp (Real.pi * Real.exp (31 / 160 : ℝ) - (77 / 1600 : ℝ)) ≤
      (431687975013 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell154_denomUpper
    linarith [hpThetaJensenCell154_product_upper]
  have hi : (1 / (431687975013 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (31 / 160 : ℝ) - (77 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (431687975013 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (431687975013 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((77 / 1600 : ℝ) - Real.pi * Real.exp (31 / 160 : ℝ)) := by
    rw [show (77 / 1600 : ℝ) - Real.pi * Real.exp (31 / 160 : ℝ) =
      -(Real.pi * Real.exp (31 / 160 : ℝ) - (77 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (77 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (77 / 400 : ℝ)) := by
    have h := hpThetaJensenCell154_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (431687975013 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell154_endpointUpper :
    hpThetaJensenKernelEndpointUpper (77 / 800 : ℝ) (31 / 320 : ℝ) ≤ (16473391587 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (31 / 160 : ℝ)) (38132429541914617 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (31 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell154_product_upper
  have hD : (26843857833 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (77 / 400 : ℝ) - (31 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell154_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell154_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (77 / 400 : ℝ) - (31 / 640 : ℝ)) ≤
      (1 / (26843857833 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (26843857833 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((31 / 640 : ℝ) - Real.pi * Real.exp (77 / 400 : ℝ)) ≤
      (2 / (26843857833 / 625000000 : ℝ) : ℝ) := by
    rw [show (31 / 640 : ℝ) - Real.pi * Real.exp (77 / 400 : ℝ) =
      -(Real.pi * Real.exp (77 / 400 : ℝ) - (31 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (38132429541914617 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (38132429541914617 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell154_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (77 / 800 : ℝ) (31 / 320 : ℝ)) :
    (16292858171 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (16473391587 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell154_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell154_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell155_leftExp :
    (12137927967 / 10000000000 : ℝ) ≤ Real.exp (31 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (31 / 160 : ℝ) (1006073054169 / 1000000000000 : ℝ)
    (12137927967 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell155_rightExp :
    Real.exp (39 / 200 : ℝ) ≤ (6076554933 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (39 / 200 : ℝ) (1006112354667 / 1000000000000 : ℝ)
    (6076554933 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell155_denomUpper :
    Real.exp (18847874941628269 / 5000000000000000 : ℝ) ≤ (433616317203 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (18847874941628269 / 5000000000000000 : ℝ) (562509102859
    / 500000000000 : ℝ) (433616317203 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell155_denomLower :
    (215708865191 / 5000000000 : ℝ) ≤ Real.exp (4705614674712933 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4705614674712933 / 1250000000000000 : ℝ) (1124839509061
    / 1000000000000 : ℝ) (215708865191 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell155_product_lower :
    (4766552174712933 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (31 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell155_leftExp
    (by norm_num : (0 : ℝ) ≤ (12137927967 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell155_product_upper :
    Real.pi * Real.exp (39 / 200 : ℝ) ≤ (19090062441628269 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell155_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell155_endpointLower :
    (16274202987 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (31 / 320 : ℝ) (39 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4766552174712933 / 1250000000000000 : ℝ) (Real.pi * Real.exp (31 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell155_product_lower
  have hD : Real.exp (Real.pi * Real.exp (39 / 200 : ℝ) - (31 / 640 : ℝ)) ≤
      (433616317203 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell155_denomUpper
    linarith [hpThetaJensenCell155_product_upper]
  have hi : (1 / (433616317203 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (39 / 200 : ℝ) - (31 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (433616317203 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (433616317203 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((31 / 640 : ℝ) - Real.pi * Real.exp (39 / 200 : ℝ)) := by
    rw [show (31 / 640 : ℝ) - Real.pi * Real.exp (39 / 200 : ℝ) =
      -(Real.pi * Real.exp (39 / 200 : ℝ) - (31 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (31 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (31 / 160 : ℝ)) := by
    have h := hpThetaJensenCell155_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (433616317203 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell155_endpointUpper :
    hpThetaJensenKernelEndpointUpper (31 / 320 : ℝ) (39 / 400 : ℝ) ≤ (8227300137 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (39 / 200 : ℝ)) (19090062441628269 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (39 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell155_product_upper
  have hD : (215708865191 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (31 / 160 : ℝ) - (39 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell155_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell155_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (31 / 160 : ℝ) - (39 / 800 : ℝ)) ≤
      (1 / (215708865191 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (215708865191 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((39 / 800 : ℝ) - Real.pi * Real.exp (31 / 160 : ℝ)) ≤
      (2 / (215708865191 / 5000000000 : ℝ) : ℝ) := by
    rw [show (39 / 800 : ℝ) - Real.pi * Real.exp (31 / 160 : ℝ) =
      -(Real.pi * Real.exp (31 / 160 : ℝ) - (39 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (19090062441628269 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (19090062441628269 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell155_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (31 / 320 : ℝ) (39 / 400 : ℝ)) :
    (16274202987 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8227300137 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell155_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell155_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell156_leftExp :
    (1519138733 / 1250000000 : ℝ) ≤ Real.exp (39 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (39 / 200 : ℝ) (503056177333 / 500000000000 : ℝ)
    (1519138733 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell156_rightExp :
    Real.exp (157 / 800 : ℝ) ≤ (12168310751 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (157 / 800 : ℝ) (503075828349 / 500000000000 : ℝ)
    (12168310751 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell156_denomUpper :
    Real.exp (37740379877166343 / 10000000000000000 : ℝ) ≤ (8711117429 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (37740379877166343 / 10000000000000000 : ℝ)
    (1125175121521 / 1000000000000 : ℝ) (8711117429 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell156_denomLower :
    (433344864743 / 10000000000 : ℝ) ≤ Real.exp (588898245685367 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (588898245685367 / 156250000000000 : ℝ) (281249047543 /
    250000000000 : ℝ) (433344864743 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell156_product_lower :
    (596564261310367 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (39 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell156_leftExp
    (by norm_num : (0 : ℝ) ≤ (1519138733 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell156_product_upper :
    Real.pi * Real.exp (157 / 800 : ℝ) ≤ (38227879877166343 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell156_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell156_endpointLower :
    (2031930631 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (39 / 400 : ℝ) (157 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (596564261310367 / 156250000000000 : ℝ) (Real.pi * Real.exp (39 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell156_product_lower
  have hD : Real.exp (Real.pi * Real.exp (157 / 800 : ℝ) - (39 / 800 : ℝ)) ≤
      (8711117429 / 200000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell156_denomUpper
    linarith [hpThetaJensenCell156_product_upper]
  have hi : (1 / (8711117429 / 200000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (157 / 800 : ℝ) - (39 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (8711117429 / 200000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (8711117429 / 200000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((39 / 800 : ℝ) - Real.pi * Real.exp (157 / 800 : ℝ)) := by
    rw [show (39 / 800 : ℝ) - Real.pi * Real.exp (157 / 800 : ℝ) =
      -(Real.pi * Real.exp (157 / 800 : ℝ) - (39 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (39 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (39 / 200 : ℝ)) := by
    have h := hpThetaJensenCell156_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (8711117429 / 200000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell156_endpointUpper :
    hpThetaJensenKernelEndpointUpper (39 / 400 : ℝ) (157 / 1600 : ℝ) ≤ (1643570509 / 1000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (157 / 800 : ℝ)) (38227879877166343 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (157 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell156_product_upper
  have hD : (433344864743 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (39 / 200 : ℝ) - (157 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell156_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell156_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (39 / 200 : ℝ) - (157 / 3200 : ℝ)) ≤
      (1 / (433344864743 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (433344864743 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((157 / 3200 : ℝ) - Real.pi * Real.exp (39 / 200 : ℝ)) ≤
      (2 / (433344864743 / 10000000000 : ℝ) : ℝ) := by
    rw [show (157 / 3200 : ℝ) - Real.pi * Real.exp (39 / 200 : ℝ) =
      -(Real.pi * Real.exp (39 / 200 : ℝ) - (157 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (38227879877166343 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (38227879877166343 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell156_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (39 / 400 : ℝ) (157 / 1600 : ℝ)) :
    (2031930631 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1643570509 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell156_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell156_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell157_leftExp :
    (48673243 / 40000000 : ℝ) ≤ Real.exp (157 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (157 / 800 : ℝ) (1006151656697 / 1000000000000 : ℝ)
    (48673243 / 40000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell157_rightExp :
    Real.exp (79 / 400 : ℝ) ≤ (243670613 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (79 / 400 : ℝ) (201238192053 / 200000000000 : ℝ)
    (243670613 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell157_denomUpper :
    Real.exp (755701392106509 / 200000000000000 : ℝ) ≤ (87501342939 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (755701392106509 / 200000000000000 : ℝ) (1125332269277 /
    1000000000000 : ℝ) (87501342939 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell157_denomLower :
    (435283204267 / 10000000000 : ℝ) ≤ Real.exp (18867058852857 / 5000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (18867058852857 / 5000000000000 : ℝ) (562576551431 /
    500000000000 : ℝ) (435283204267 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell157_product_lower :
    (19113933852857 / 5000000000000 : ℝ) ≤ Real.pi * Real.exp (157 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell157_leftExp
    (by norm_num : (0 : ℝ) ≤ (48673243 / 40000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell157_product_upper :
    Real.pi * Real.exp (79 / 400 : ℝ) ≤ (765513892106509 / 200000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell157_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell157_endpointLower :
    (16236584699 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (157 / 1600 : ℝ) (79 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (19113933852857 / 5000000000000 : ℝ) (Real.pi * Real.exp (157 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell157_product_lower
  have hD : Real.exp (Real.pi * Real.exp (79 / 400 : ℝ) - (157 / 3200 : ℝ)) ≤
      (87501342939 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell157_denomUpper
    linarith [hpThetaJensenCell157_product_upper]
  have hi : (1 / (87501342939 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (79 / 400 : ℝ) - (157 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (87501342939 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (87501342939 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((157 / 3200 : ℝ) - Real.pi * Real.exp (79 / 400 : ℝ)) := by
    rw [show (157 / 3200 : ℝ) - Real.pi * Real.exp (79 / 400 : ℝ) =
      -(Real.pi * Real.exp (79 / 400 : ℝ) - (157 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (157 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (157 / 800 : ℝ)) := by
    have h := hpThetaJensenCell157_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (87501342939 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell157_endpointUpper :
    hpThetaJensenKernelEndpointUpper (157 / 1600 : ℝ) (79 / 800 : ℝ) ≤ (1641670641 / 1000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (79 / 400 : ℝ)) (765513892106509 / 200000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (79 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell157_product_upper
  have hD : (435283204267 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (157 / 800 : ℝ) - (79 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell157_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell157_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (157 / 800 : ℝ) - (79 / 1600 : ℝ)) ≤
      (1 / (435283204267 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (435283204267 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((79 / 1600 : ℝ) - Real.pi * Real.exp (157 / 800 : ℝ)) ≤
      (2 / (435283204267 / 10000000000 : ℝ) : ℝ) := by
    rw [show (79 / 1600 : ℝ) - Real.pi * Real.exp (157 / 800 : ℝ) =
      -(Real.pi * Real.exp (157 / 800 : ℝ) - (79 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (765513892106509 / 200000000000000 : ℝ) ^ 2 - 6 *
      (765513892106509 / 200000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell157_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (157 / 1600 : ℝ) (79 / 800 : ℝ)) :
    (16236584699 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1641670641 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell157_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell157_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell158_leftExp :
    (12183530649 / 10000000000 : ℝ) ≤ Real.exp (79 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (79 / 400 : ℝ) (125773870033 / 125000000000 : ℝ)
    (12183530649 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell158_rightExp :
    Real.exp (159 / 800 : ℝ) ≤ (6099384793 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (159 / 800 : ℝ) (1006230265367 / 1000000000000 : ℝ)
    (6099384793 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell158_denomUpper :
    Real.exp (18914909569995249 / 5000000000000000 : ℝ) ≤ (439468924007 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (18914909569995249 / 5000000000000000 : ℝ) (1125489649329
    / 1000000000000 : ℝ) (439468924007 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell158_denomLower :
    (218616412787 / 5000000000 : ℝ) ≤ Real.exp (4722350927331651 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4722350927331651 / 1250000000000000 : ℝ) (1125310247489
    / 1000000000000 : ℝ) (218616412787 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell158_product_lower :
    (4784460302331651 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (79 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell158_leftExp
    (by norm_num : (0 : ℝ) ≤ (12183530649 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell158_product_upper :
    Real.pi * Real.exp (159 / 800 : ℝ) ≤ (19161784569995249 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell158_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell158_endpointLower :
    (1621762231 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (79 / 800 : ℝ) (159 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4784460302331651 / 1250000000000000 : ℝ) (Real.pi * Real.exp (79 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell158_product_lower
  have hD : Real.exp (Real.pi * Real.exp (159 / 800 : ℝ) - (79 / 1600 : ℝ)) ≤
      (439468924007 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell158_denomUpper
    linarith [hpThetaJensenCell158_product_upper]
  have hi : (1 / (439468924007 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (159 / 800 : ℝ) - (79 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (439468924007 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (439468924007 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((79 / 1600 : ℝ) - Real.pi * Real.exp (159 / 800 : ℝ)) := by
    rw [show (79 / 1600 : ℝ) - Real.pi * Real.exp (159 / 800 : ℝ) =
      -(Real.pi * Real.exp (159 / 800 : ℝ) - (79 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (79 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (79 / 400 : ℝ)) := by
    have h := hpThetaJensenCell158_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (439468924007 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell158_endpointUpper :
    hpThetaJensenKernelEndpointUpper (79 / 800 : ℝ) (159 / 1600 : ℝ) ≤ (8198802297 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (159 / 800 : ℝ)) (19161784569995249 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (159 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell158_product_upper
  have hD : (218616412787 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (79 / 400 : ℝ) - (159 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell158_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell158_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (79 / 400 : ℝ) - (159 / 3200 : ℝ)) ≤
      (1 / (218616412787 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (218616412787 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((159 / 3200 : ℝ) - Real.pi * Real.exp (79 / 400 : ℝ)) ≤
      (2 / (218616412787 / 5000000000 : ℝ) : ℝ) := by
    rw [show (159 / 3200 : ℝ) - Real.pi * Real.exp (79 / 400 : ℝ) =
      -(Real.pi * Real.exp (79 / 400 : ℝ) - (159 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (19161784569995249 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (19161784569995249 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell158_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (79 / 800 : ℝ) (159 / 1600 : ℝ)) :
    (1621762231 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8198802297 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell158_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell158_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell159_leftExp :
    (2439753917 / 2000000000 : ℝ) ≤ Real.exp (159 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (159 / 800 : ℝ) (503115132683 / 500000000000 : ℝ)
    (2439753917 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell159_rightExp :
    Real.exp (1 / 5 : ℝ) ≤ (6107013791 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1 / 5 : ℝ) (251567393001 / 250000000000 : ℝ)
    (6107013791 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell159_denomUpper :
    Real.exp (18937314276709063 / 5000000000000000 : ℝ) ≤ (441442577083 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (18937314276709063 / 5000000000000000 : ℝ) (1125647262023
    / 1000000000000 : ℝ) (441442577083 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell159_denomLower :
    (219596902911 / 5000000000 : ℝ) ≤ Real.exp (945588923451983 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (945588923451983 / 250000000000000 : ℝ) (1125467624407 /
    1000000000000 : ℝ) (219596902911 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell159_product_lower :
    (958088923451983 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (159 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell159_leftExp
    (by norm_num : (0 : ℝ) ≤ (2439753917 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell159_product_upper :
    Real.pi * Real.exp (1 / 5 : ℝ) ≤ (19185751776709063 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell159_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell159_endpointLower :
    (16198558249 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (159 / 1600 : ℝ) (1 / 10 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (958088923451983 / 250000000000000 : ℝ) (Real.pi * Real.exp (159 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell159_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1 / 5 : ℝ) - (159 / 3200 : ℝ)) ≤
      (441442577083 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell159_denomUpper
    linarith [hpThetaJensenCell159_product_upper]
  have hi : (1 / (441442577083 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1 / 5 : ℝ) - (159 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (441442577083 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (441442577083 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((159 / 3200 : ℝ) - Real.pi * Real.exp (1 / 5 : ℝ)) := by
    rw [show (159 / 3200 : ℝ) - Real.pi * Real.exp (1 / 5 : ℝ) =
      -(Real.pi * Real.exp (1 / 5 : ℝ) - (159 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (159 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (159 / 800 : ℝ)) := by
    have h := hpThetaJensenCell159_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (441442577083 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell159_endpointUpper :
    hpThetaJensenKernelEndpointUpper (159 / 1600 : ℝ) (1 / 10 : ℝ) ≤ (8189200003 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1 / 5 : ℝ)) (19185751776709063 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1 / 10 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell159_product_upper
  have hD : (219596902911 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (159 / 800 : ℝ) - (1 / 20 : ℝ)) := by
    apply le_trans hpThetaJensenCell159_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell159_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (159 / 800 : ℝ) - (1 / 20 : ℝ)) ≤
      (1 / (219596902911 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (219596902911 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1 / 20 : ℝ) - Real.pi * Real.exp (159 / 800 : ℝ)) ≤
      (2 / (219596902911 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1 / 20 : ℝ) - Real.pi * Real.exp (159 / 800 : ℝ) =
      -(Real.pi * Real.exp (159 / 800 : ℝ) - (1 / 20 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (19185751776709063 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (19185751776709063 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell159_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (159 / 1600 : ℝ) (1 / 10 : ℝ)) :
    (16198558249 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8189200003 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell159_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell159_endpointUpper

def hpThetaJensenCellsBatch007Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (16543042043 / 10000000000 : ℝ)
  | 1 => (1032866411 / 625000000 : ℝ)
  | 2 => (825428773 / 500000000 : ℝ)
  | 3 => (16491181033 / 10000000000 : ℝ)
  | 4 => (16473679637 / 10000000000 : ℝ)
  | 5 => (16456071609 / 10000000000 : ℝ)
  | 6 => (16438357291 / 10000000000 : ℝ)
  | 7 => (8210268517 / 5000000000 : ℝ)
  | 8 => (8201305591 / 5000000000 : ℝ)
  | 9 => (8192290041 / 5000000000 : ℝ)
  | 10 => (3273288817 / 2000000000 : ℝ)
  | 11 => (8174101771 / 5000000000 : ℝ)
  | 12 => (2041232351 / 1250000000 : ℝ)
  | 13 => (16311410229 / 10000000000 : ℝ)
  | 14 => (16292858171 / 10000000000 : ℝ)
  | 15 => (16274202987 / 10000000000 : ℝ)
  | 16 => (2031930631 / 1250000000 : ℝ)
  | 17 => (16236584699 / 10000000000 : ℝ)
  | 18 => (1621762231 / 1000000000 : ℝ)
  | 19 => (16198558249 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch007Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (16725364879 / 10000000000 : ℝ)
  | 1 => (4177016213 / 2500000000 : ℝ)
  | 2 => (16690656057 / 10000000000 : ℝ)
  | 3 => (4168284707 / 2500000000 : ℝ)
  | 4 => (3331102701 / 2000000000 : ℝ)
  | 5 => (8318890219 / 5000000000 : ℝ)
  | 6 => (16619939969 / 10000000000 : ℝ)
  | 7 => (8300996221 / 5000000000 : ℝ)
  | 8 => (8291969101 / 5000000000 : ℝ)
  | 9 => (8282888803 / 5000000000 : ℝ)
  | 10 => (8273755499 / 5000000000 : ℝ)
  | 11 => (16529138739 / 10000000000 : ℝ)
  | 12 => (2063832647 / 1250000000 : ℝ)
  | 13 => (659683147 / 400000000 : ℝ)
  | 14 => (16473391587 / 10000000000 : ℝ)
  | 15 => (8227300137 / 5000000000 : ℝ)
  | 16 => (1643570509 / 1000000000 : ℝ)
  | 17 => (1641670641 / 1000000000 : ℝ)
  | 18 => (8198802297 / 5000000000 : ℝ)
  | 19 => (8189200003 / 5000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch007_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((140 : ℝ) + (j.val : ℝ)) / 1600)
      (((140 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch007Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch007Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell140_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell141_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell142_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell143_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell144_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell145_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell146_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell147_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell148_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell149_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell150_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell151_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell152_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell153_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell154_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell155_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell156_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell157_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell158_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell159_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper] at h ⊢
    exact h

end HodgeProofHP
