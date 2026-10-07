import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell720_leftExp :
    (24596031111 / 10000000000 : ℝ) ≤ Real.exp (9 / 10 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9 / 10 : ℝ) (257131060479 / 250000000000 : ℝ)
    (24596031111 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell720_rightExp :
    Real.exp (721 / 800 : ℝ) ≤ (197014363 / 80000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (721 / 800 : ℝ) (102856441943 / 100000000000 : ℝ)
    (197014363 / 80000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell720_denomUpper :
    Real.exp (600938943700259 / 80000000000000 : ℝ) ≤ (1829388059623 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (600938943700259 / 80000000000000 : ℝ) (1264582179687 /
    1000000000000 : ℝ) (1829388059623 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell720_denomLower :
    (9056109297503 / 5000000000 : ℝ) ≤ Real.exp (9377196196258589 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9377196196258589 / 1250000000000000 : ℝ) (316046963991 /
    250000000000 : ℝ) (9056109297503 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell720_product_lower :
    (9658836821258589 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (9 / 10 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell720_leftExp
    (by norm_num : (0 : ℝ) ≤ (24596031111 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell720_product_upper :
    Real.pi * Real.exp (721 / 800 : ℝ) ≤ (618938943700259 / 80000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell720_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell720_endpointLower :
    (420835791 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (9 / 20 : ℝ) (721 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9658836821258589 / 1250000000000000 : ℝ) (Real.pi * Real.exp (9 / 10 : ℝ))
    (by norm_num) hpThetaJensenCell720_product_lower
  have hD : Real.exp (Real.pi * Real.exp (721 / 800 : ℝ) - (9 / 40 : ℝ)) ≤
      (1829388059623 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell720_denomUpper
    linarith [hpThetaJensenCell720_product_upper]
  have hi : (1 / (1829388059623 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (721 / 800 : ℝ) - (9 / 40 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1829388059623 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1829388059623 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((9 / 40 : ℝ) - Real.pi * Real.exp (721 / 800 : ℝ)) := by
    rw [show (9 / 40 : ℝ) - Real.pi * Real.exp (721 / 800 : ℝ) =
      -(Real.pi * Real.exp (721 / 800 : ℝ) - (9 / 40 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (9 / 10 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (9 / 10 : ℝ)) := by
    have h := hpThetaJensenCell720_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1829388059623 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell720_endpointUpper :
    hpThetaJensenKernelEndpointUpper (9 / 20 : ℝ) (721 / 1600 : ℝ) ≤ (267107333 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (721 / 800 : ℝ)) (618938943700259 / 80000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (721 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell720_product_upper
  have hD : (9056109297503 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (9 / 10 : ℝ) - (721 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell720_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell720_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (9 / 10 : ℝ) - (721 / 3200 : ℝ)) ≤
      (1 / (9056109297503 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (9056109297503 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((721 / 3200 : ℝ) - Real.pi * Real.exp (9 / 10 : ℝ)) ≤
      (2 / (9056109297503 / 5000000000 : ℝ) : ℝ) := by
    rw [show (721 / 3200 : ℝ) - Real.pi * Real.exp (9 / 10 : ℝ) =
      -(Real.pi * Real.exp (9 / 10 : ℝ) - (721 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (618938943700259 / 80000000000000 : ℝ) ^ 2 - 6 *
      (618938943700259 / 80000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell720_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (9 / 20 : ℝ) (721 / 1600 : ℝ)) :
    (420835791 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (267107333 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell720_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell720_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell721_leftExp :
    (24626795373 / 10000000000 : ℝ) ≤ Real.exp (721 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (721 / 800 : ℝ) (1028564419429 / 1000000000000 : ℝ)
    (24626795373 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell721_rightExp :
    Real.exp (361 / 400 : ℝ) ≤ (24657598117 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (361 / 400 : ℝ) (64287787407 / 62500000000 : ℝ)
    (24657598117 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell721_denomUpper :
    Real.exp (75211012641180381 / 10000000000000000 : ℝ) ≤ (18465997687941 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (75211012641180381 / 10000000000000000 : ℝ) (126495230069
    / 100000000000 : ℝ) (18465997687941 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell721_denomLower :
    (1142650341091 / 625000000 : ℝ) ≤ Real.exp (9388886666181727 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9388886666181727 / 1250000000000000 : ℝ) (1264557383713
    / 1000000000000 : ℝ) (1142650341091 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell721_product_lower :
    (9670917916181727 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (721 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell721_leftExp
    (by norm_num : (0 : ℝ) ≤ (24626795373 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell721_product_upper :
    Real.pi * Real.exp (361 / 400 : ℝ) ≤ (77464137641180381 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell721_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell721_endpointLower :
    (2090413199 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (721 / 1600 : ℝ) (361 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9670917916181727 / 1250000000000000 : ℝ) (Real.pi * Real.exp (721 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell721_product_lower
  have hD : Real.exp (Real.pi * Real.exp (361 / 400 : ℝ) - (721 / 3200 : ℝ)) ≤
      (18465997687941 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell721_denomUpper
    linarith [hpThetaJensenCell721_product_upper]
  have hi : (1 / (18465997687941 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (361 / 400 : ℝ) - (721 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (18465997687941 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (18465997687941 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((721 / 3200 : ℝ) - Real.pi * Real.exp (361 / 400 : ℝ)) := by
    rw [show (721 / 3200 : ℝ) - Real.pi * Real.exp (361 / 400 : ℝ) =
      -(Real.pi * Real.exp (361 / 400 : ℝ) - (721 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (721 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (721 / 800 : ℝ)) := by
    have h := hpThetaJensenCell721_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (18465997687941 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell721_endpointUpper :
    hpThetaJensenKernelEndpointUpper (721 / 1600 : ℝ) (361 / 800 : ℝ) ≤ (424580759 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (361 / 400 : ℝ)) (77464137641180381 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (361 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell721_product_upper
  have hD : (1142650341091 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (721 / 800 : ℝ) - (361 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell721_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell721_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (721 / 800 : ℝ) - (361 / 1600 : ℝ)) ≤
      (1 / (1142650341091 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1142650341091 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((361 / 1600 : ℝ) - Real.pi * Real.exp (721 / 800 : ℝ)) ≤
      (2 / (1142650341091 / 625000000 : ℝ) : ℝ) := by
    rw [show (361 / 1600 : ℝ) - Real.pi * Real.exp (721 / 800 : ℝ) =
      -(Real.pi * Real.exp (721 / 800 : ℝ) - (361 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (77464137641180381 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (77464137641180381 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell721_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (721 / 1600 : ℝ) (361 / 800 : ℝ)) :
    (2090413199 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (424580759 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell721_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell721_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell722_leftExp :
    (4931519623 / 2000000000 : ℝ) ≤ Real.exp (361 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (361 / 400 : ℝ) (1028604598511 / 1000000000000 : ℝ)
    (4931519623 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell722_rightExp :
    Real.exp (723 / 800 : ℝ) ≤ (12344219693 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (723 / 800 : ℝ) (257161194791 / 250000000000 : ℝ)
    (12344219693 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell722_denomUpper :
    Real.exp (37652389177990949 / 5000000000000000 : ℝ) ≤ (4659989936127 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (37652389177990949 / 5000000000000000 : ℝ) (632661504307
    / 500000000000 : ℝ) (4659989936127 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell722_denomLower :
    (18454414529083 / 10000000000 : ℝ) ≤ Real.exp (1880118449432477 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1880118449432477 / 250000000000000 : ℝ) (1264927497337 /
    1000000000000 : ℝ) (18454414529083 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell722_product_lower :
    (1936602824432477 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (361 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell722_leftExp
    (by norm_num : (0 : ℝ) ≤ (4931519623 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell722_product_upper :
    Real.pi * Real.exp (723 / 800 : ℝ) ≤ (38780514177990949 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell722_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell722_endpointLower :
    (519177849 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (361 / 800 : ℝ) (723 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1936602824432477 / 250000000000000 : ℝ) (Real.pi * Real.exp (361 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell722_product_lower
  have hD : Real.exp (Real.pi * Real.exp (723 / 800 : ℝ) - (361 / 1600 : ℝ)) ≤
      (4659989936127 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell722_denomUpper
    linarith [hpThetaJensenCell722_product_upper]
  have hi : (1 / (4659989936127 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (723 / 800 : ℝ) - (361 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4659989936127 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4659989936127 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((361 / 1600 : ℝ) - Real.pi * Real.exp (723 / 800 : ℝ)) := by
    rw [show (361 / 1600 : ℝ) - Real.pi * Real.exp (723 / 800 : ℝ) =
      -(Real.pi * Real.exp (723 / 800 : ℝ) - (361 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (361 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (361 / 400 : ℝ)) := by
    have h := hpThetaJensenCell722_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4659989936127 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell722_endpointUpper :
    hpThetaJensenKernelEndpointUpper (361 / 800 : ℝ) (723 / 1600 : ℝ) ≤ (2109013581 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (723 / 800 : ℝ)) (38780514177990949 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (723 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell722_product_upper
  have hD : (18454414529083 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (361 / 400 : ℝ) - (723 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell722_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell722_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (361 / 400 : ℝ) - (723 / 3200 : ℝ)) ≤
      (1 / (18454414529083 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (18454414529083 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((723 / 3200 : ℝ) - Real.pi * Real.exp (361 / 400 : ℝ)) ≤
      (2 / (18454414529083 / 10000000000 : ℝ) : ℝ) := by
    rw [show (723 / 3200 : ℝ) - Real.pi * Real.exp (361 / 400 : ℝ) =
      -(Real.pi * Real.exp (361 / 400 : ℝ) - (723 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (38780514177990949 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (38780514177990949 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell722_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (361 / 800 : ℝ) (723 / 1600 : ℝ)) :
    (519177849 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2109013581 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell722_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell722_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell723_leftExp :
    (3086054923 / 1250000000 : ℝ) ≤ Real.exp (723 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (723 / 800 : ℝ) (1028644779163 / 1000000000000 : ℝ)
    (3086054923 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell723_rightExp :
    Real.exp (181 / 200 : ℝ) ≤ (386239363 / 156250000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (181 / 200 : ℝ) (514342480693 / 500000000000 : ℝ)
    (386239363 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell723_denomUpper :
    Real.exp (1178104144750259 / 156250000000000 : ℝ) ≤ (9407894336701 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1178104144750259 / 156250000000000 : ℝ) (1265694304533 /
    1000000000000 : ℝ) (9407894336701 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell723_denomLower :
    (9314133703507 / 5000000000 : ℝ) ≤ Real.exp (1176539119707177 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1176539119707177 / 156250000000000 : ℝ) (126529819787 /
    100000000000 : ℝ) (9314133703507 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell723_product_lower :
    (1211890682207177 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (723 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell723_leftExp
    (by norm_num : (0 : ℝ) ≤ (3086054923 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell723_product_upper :
    Real.pi * Real.exp (181 / 200 : ℝ) ≤ (1213406879125259 / 156250000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell723_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell723_endpointLower :
    (12894209 / 62500000 : ℝ) ≤ hpThetaTraceEndpointLower (723 / 1600 : ℝ) (181 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1211890682207177 / 156250000000000 : ℝ) (Real.pi * Real.exp (723 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell723_product_lower
  have hD : Real.exp (Real.pi * Real.exp (181 / 200 : ℝ) - (723 / 3200 : ℝ)) ≤
      (9407894336701 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell723_denomUpper
    linarith [hpThetaJensenCell723_product_upper]
  have hi : (1 / (9407894336701 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (181 / 200 : ℝ) - (723 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (9407894336701 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (9407894336701 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((723 / 3200 : ℝ) - Real.pi * Real.exp (181 / 200 : ℝ)) := by
    rw [show (723 / 3200 : ℝ) - Real.pi * Real.exp (181 / 200 : ℝ) =
      -(Real.pi * Real.exp (181 / 200 : ℝ) - (723 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (723 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (723 / 800 : ℝ)) := by
    have h := hpThetaJensenCell723_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (9407894336701 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell723_endpointUpper :
    hpThetaJensenKernelEndpointUpper (723 / 1600 : ℝ) (181 / 400 : ℝ) ≤ (1047593959 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (181 / 200 : ℝ)) (1213406879125259 / 156250000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (181 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell723_product_upper
  have hD : (9314133703507 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (723 / 800 : ℝ) - (181 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell723_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell723_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (723 / 800 : ℝ) - (181 / 800 : ℝ)) ≤
      (1 / (9314133703507 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (9314133703507 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((181 / 800 : ℝ) - Real.pi * Real.exp (723 / 800 : ℝ)) ≤
      (2 / (9314133703507 / 5000000000 : ℝ) : ℝ) := by
    rw [show (181 / 800 : ℝ) - Real.pi * Real.exp (723 / 800 : ℝ) =
      -(Real.pi * Real.exp (723 / 800 : ℝ) - (181 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1213406879125259 / 156250000000000 : ℝ) ^ 2 - 6 *
      (1213406879125259 / 156250000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell723_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (723 / 1600 : ℝ) (181 / 400 : ℝ)) :
    (12894209 / 62500000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1047593959 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell723_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell723_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell724_leftExp :
    (2471931923 / 1000000000 : ℝ) ≤ Real.exp (181 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (181 / 200 : ℝ) (205736992277 / 200000000000 : ℝ)
    (2471931923 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell724_rightExp :
    Real.exp (29 / 32 : ℝ) ≤ (24750237701 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (29 / 32 : ℝ) (1028725145177 / 1000000000000 : ℝ)
    (24750237701 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell724_denomUpper :
    Real.exp (75492673509797693 / 10000000000000000 : ℝ) ≤ (18993506640833 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (75492673509797693 / 10000000000000000 : ℝ) (39564568421
    / 31250000000 : ℝ) (18993506640833 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell724_denomLower :
    (3760797196993 / 2000000000 : ℝ) ≤ Real.exp (942404881730177 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (942404881730177 / 125000000000000 : ℝ) (632834743193 /
    500000000000 : ℝ) (3760797196993 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell724_product_lower :
    (970725194230177 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (181 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell724_leftExp
    (by norm_num : (0 : ℝ) ≤ (2471931923 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell724_product_upper :
    Real.pi * Real.exp (29 / 32 : ℝ) ≤ (77755173509797693 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell724_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell724_endpointLower :
    (81979969 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (181 / 400 : ℝ) (29 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (970725194230177 / 125000000000000 : ℝ) (Real.pi * Real.exp (181 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell724_product_lower
  have hD : Real.exp (Real.pi * Real.exp (29 / 32 : ℝ) - (181 / 800 : ℝ)) ≤
      (18993506640833 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell724_denomUpper
    linarith [hpThetaJensenCell724_product_upper]
  have hi : (1 / (18993506640833 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (29 / 32 : ℝ) - (181 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (18993506640833 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (18993506640833 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((181 / 800 : ℝ) - Real.pi * Real.exp (29 / 32 : ℝ)) := by
    rw [show (181 / 800 : ℝ) - Real.pi * Real.exp (29 / 32 : ℝ) =
      -(Real.pi * Real.exp (29 / 32 : ℝ) - (181 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (181 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (181 / 200 : ℝ)) := by
    have h := hpThetaJensenCell724_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (18993506640833 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell724_endpointUpper :
    hpThetaJensenKernelEndpointUpper (181 / 400 : ℝ) (29 / 64 : ℝ) ≤ (2081426699 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (29 / 32 : ℝ)) (77755173509797693 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (29 / 64 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell724_product_upper
  have hD : (3760797196993 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (181 / 200 : ℝ) - (29 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell724_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell724_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (181 / 200 : ℝ) - (29 / 128 : ℝ)) ≤
      (1 / (3760797196993 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3760797196993 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((29 / 128 : ℝ) - Real.pi * Real.exp (181 / 200 : ℝ)) ≤
      (2 / (3760797196993 / 2000000000 : ℝ) : ℝ) := by
    rw [show (29 / 128 : ℝ) - Real.pi * Real.exp (181 / 200 : ℝ) =
      -(Real.pi * Real.exp (181 / 200 : ℝ) - (29 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (77755173509797693 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (77755173509797693 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell724_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (181 / 400 : ℝ) (29 / 64 : ℝ)) :
    (81979969 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2081426699 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell724_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell724_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell725_leftExp :
    (24750237699 / 10000000000 : ℝ) ≤ Real.exp (29 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (29 / 32 : ℝ) (128590643147 / 125000000000 : ℝ)
    (24750237699 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell725_rightExp :
    Real.exp (363 / 400 : ℝ) ≤ (12390597421 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (363 / 400 : ℝ) (514382665269 / 500000000000 : ℝ)
    (12390597421 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell725_denomUpper :
    Real.exp (37793401623631653 / 5000000000000000 : ℝ) ≤ (19173136117683 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (37793401623631653 / 5000000000000000 : ℝ) (79152416531 /
    62500000000 : ℝ) (19173136117683 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell725_denomLower :
    (18981592415707 / 10000000000 : ℝ) ≤ Real.exp (9435799844159601 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9435799844159601 / 1250000000000000 : ℝ) (1266041363911
    / 1000000000000 : ℝ) (18981592415707 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell725_product_lower :
    (9719393594159601 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (29 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell725_leftExp
    (by norm_num : (0 : ℝ) ≤ (24750237699 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell725_product_upper :
    Real.pi * Real.exp (363 / 400 : ℝ) ≤ (38926214123631653 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell725_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell725_endpointLower :
    (508997161 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (29 / 64 : ℝ) (363 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9719393594159601 / 1250000000000000 : ℝ) (Real.pi * Real.exp (29 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell725_product_lower
  have hD : Real.exp (Real.pi * Real.exp (363 / 400 : ℝ) - (29 / 128 : ℝ)) ≤
      (19173136117683 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell725_denomUpper
    linarith [hpThetaJensenCell725_product_upper]
  have hi : (1 / (19173136117683 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (363 / 400 : ℝ) - (29 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (19173136117683 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (19173136117683 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((29 / 128 : ℝ) - Real.pi * Real.exp (363 / 400 : ℝ)) := by
    rw [show (29 / 128 : ℝ) - Real.pi * Real.exp (363 / 400 : ℝ) =
      -(Real.pi * Real.exp (363 / 400 : ℝ) - (29 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (29 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (29 / 32 : ℝ)) := by
    have h := hpThetaJensenCell725_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (19173136117683 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell725_endpointUpper :
    hpThetaJensenKernelEndpointUpper (29 / 64 : ℝ) (363 / 800 : ℝ) ≤ (1033864909 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (363 / 400 : ℝ)) (38926214123631653 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (363 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell725_product_upper
  have hD : (18981592415707 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (29 / 32 : ℝ) - (363 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell725_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell725_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (29 / 32 : ℝ) - (363 / 1600 : ℝ)) ≤
      (1 / (18981592415707 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (18981592415707 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((363 / 1600 : ℝ) - Real.pi * Real.exp (29 / 32 : ℝ)) ≤
      (2 / (18981592415707 / 10000000000 : ℝ) : ℝ) := by
    rw [show (363 / 1600 : ℝ) - Real.pi * Real.exp (29 / 32 : ℝ) =
      -(Real.pi * Real.exp (29 / 32 : ℝ) - (363 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (38926214123631653 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (38926214123631653 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell725_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (29 / 64 : ℝ) (363 / 800 : ℝ)) :
    (508997161 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1033864909 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell725_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell725_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell726_leftExp :
    (619529871 / 250000000 : ℝ) ≤ Real.exp (363 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (363 / 400 : ℝ) (1028765330537 / 1000000000000 : ℝ)
    (619529871 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell726_rightExp :
    Real.exp (727 / 800 : ℝ) ≤ (24812190703 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (727 / 800 : ℝ) (257201379367 / 250000000000 : ℝ)
    (24812190703 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell726_denomUpper :
    Real.exp (75681054627209879 / 10000000000000000 : ℝ) ≤ (9677349929451 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (75681054627209879 / 10000000000000000 : ℝ) (633405865329
    / 500000000000 : ℝ) (9677349929451 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell726_denomLower :
    (9580554577773 / 5000000000 : ℝ) ≤ Real.exp (236189151436829 / 31250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (236189151436829 / 31250000000000 : ℝ) (1266413831509 /
    1000000000000 : ℝ) (9580554577773 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell726_product_lower :
    (243288760811829 / 31250000000000 : ℝ) ≤ Real.pi * Real.exp (363 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell726_leftExp
    (by norm_num : (0 : ℝ) ≤ (619529871 / 250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell726_product_upper :
    Real.pi * Real.exp (727 / 800 : ℝ) ≤ (77949804627209879 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell726_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell726_endpointLower :
    (2022541587 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (363 / 800 : ℝ) (727 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (243288760811829 / 31250000000000 : ℝ) (Real.pi * Real.exp (363 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell726_product_lower
  have hD : Real.exp (Real.pi * Real.exp (727 / 800 : ℝ) - (363 / 1600 : ℝ)) ≤
      (9677349929451 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell726_denomUpper
    linarith [hpThetaJensenCell726_product_upper]
  have hi : (1 / (9677349929451 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (727 / 800 : ℝ) - (363 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (9677349929451 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (9677349929451 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((363 / 1600 : ℝ) - Real.pi * Real.exp (727 / 800 : ℝ)) := by
    rw [show (363 / 1600 : ℝ) - Real.pi * Real.exp (727 / 800 : ℝ) =
      -(Real.pi * Real.exp (727 / 800 : ℝ) - (363 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (363 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (363 / 400 : ℝ)) := by
    have h := hpThetaJensenCell726_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (9677349929451 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell726_endpointUpper :
    hpThetaJensenKernelEndpointUpper (363 / 800 : ℝ) (727 / 1600 : ℝ) ≤ (513524291 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (727 / 800 : ℝ)) (77949804627209879 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (727 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell726_product_upper
  have hD : (9580554577773 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (363 / 400 : ℝ) - (727 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell726_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell726_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (363 / 400 : ℝ) - (727 / 3200 : ℝ)) ≤
      (1 / (9580554577773 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (9580554577773 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((727 / 3200 : ℝ) - Real.pi * Real.exp (363 / 400 : ℝ)) ≤
      (2 / (9580554577773 / 5000000000 : ℝ) : ℝ) := by
    rw [show (727 / 3200 : ℝ) - Real.pi * Real.exp (363 / 400 : ℝ) =
      -(Real.pi * Real.exp (363 / 400 : ℝ) - (727 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (77949804627209879 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (77949804627209879 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell726_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (363 / 800 : ℝ) (727 / 1600 : ℝ)) :
    (2022541587 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (513524291 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell726_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell726_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell727_leftExp :
    (12406095351 / 5000000000 : ℝ) ≤ Real.exp (727 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (727 / 800 : ℝ) (1028805517467 / 1000000000000 : ℝ)
    (12406095351 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell727_rightExp :
    Real.exp (91 / 100 : ℝ) ≤ (4968645067 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (91 / 100 : ℝ) (1028845705969 / 1000000000000 : ℝ)
    (4968645067 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell727_denomUpper :
    Real.exp (15155085561971731 / 2000000000000000 : ℝ) ≤ (9769110466447 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (15155085561971731 / 2000000000000000 : ℝ) (1267185389051
    / 1000000000000 : ℝ) (9769110466447 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell727_denomLower :
    (19342558951007 / 10000000000 : ℝ) ≤ Real.exp (4729673738242349 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4729673738242349 / 625000000000000 : ℝ) (253357378049 /
    200000000000 : ℝ) (19342558951007 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell727_product_lower :
    (4871861238242349 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (727 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell727_leftExp
    (by norm_num : (0 : ℝ) ≤ (12406095351 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell727_product_upper :
    Real.pi * Real.exp (91 / 100 : ℝ) ≤ (15609460561971731 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell727_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell727_endpointLower :
    (251144743 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (727 / 1600 : ℝ) (91 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4871861238242349 / 625000000000000 : ℝ) (Real.pi * Real.exp (727 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell727_product_lower
  have hD : Real.exp (Real.pi * Real.exp (91 / 100 : ℝ) - (727 / 3200 : ℝ)) ≤
      (9769110466447 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell727_denomUpper
    linarith [hpThetaJensenCell727_product_upper]
  have hi : (1 / (9769110466447 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (91 / 100 : ℝ) - (727 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (9769110466447 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (9769110466447 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((727 / 3200 : ℝ) - Real.pi * Real.exp (91 / 100 : ℝ)) := by
    rw [show (727 / 3200 : ℝ) - Real.pi * Real.exp (91 / 100 : ℝ) =
      -(Real.pi * Real.exp (91 / 100 : ℝ) - (727 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (727 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (727 / 800 : ℝ)) := by
    have h := hpThetaJensenCell727_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (9769110466447 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell727_endpointUpper :
    hpThetaJensenKernelEndpointUpper (727 / 1600 : ℝ) (91 / 200 : ℝ) ≤ (2040528629 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (91 / 100 : ℝ)) (15609460561971731 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (91 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell727_product_upper
  have hD : (19342558951007 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (727 / 800 : ℝ) - (91 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell727_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell727_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (727 / 800 : ℝ) - (91 / 400 : ℝ)) ≤
      (1 / (19342558951007 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (19342558951007 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((91 / 400 : ℝ) - Real.pi * Real.exp (727 / 800 : ℝ)) ≤
      (2 / (19342558951007 / 10000000000 : ℝ) : ℝ) := by
    rw [show (91 / 400 : ℝ) - Real.pi * Real.exp (727 / 800 : ℝ) =
      -(Real.pi * Real.exp (727 / 800 : ℝ) - (91 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (15609460561971731 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (15609460561971731 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell727_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (727 / 1600 : ℝ) (91 / 200 : ℝ)) :
    (251144743 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2040528629 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell727_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell727_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell728_leftExp :
    (24843225333 / 10000000000 : ℝ) ≤ Real.exp (91 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (91 / 100 : ℝ) (64302856623 / 62500000000 : ℝ)
    (24843225333 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell728_rightExp :
    Real.exp (729 / 800 : ℝ) ≤ (24874298783 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (729 / 800 : ℝ) (1028885896039 / 1000000000000 : ℝ)
    (24874298783 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell728_denomUpper :
    Real.exp (75869922936581319 / 10000000000000000 : ℝ) ≤ (9861861334613 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (75869922936581319 / 10000000000000000 : ℝ)
    (1267559640693 / 1000000000000 : ℝ) (9861861334613 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell728_denomLower :
    (19525964838423 / 10000000000 : ℝ) ≤ Real.exp (9471144120043767 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9471144120043767 / 1250000000000000 : ℝ) (158395067647 /
    125000000000 : ℝ) (19525964838423 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell728_product_lower :
    (9755909745043767 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (91 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell728_leftExp
    (by norm_num : (0 : ℝ) ≤ (24843225333 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell728_product_upper :
    Real.pi * Real.exp (729 / 800 : ℝ) ≤ (78144922936581319 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell728_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell728_endpointLower :
    (399167521 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (91 / 200 : ℝ) (729 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9755909745043767 / 1250000000000000 : ℝ) (Real.pi * Real.exp (91 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell728_product_lower
  have hD : Real.exp (Real.pi * Real.exp (729 / 800 : ℝ) - (91 / 400 : ℝ)) ≤
      (9861861334613 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell728_denomUpper
    linarith [hpThetaJensenCell728_product_upper]
  have hi : (1 / (9861861334613 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (729 / 800 : ℝ) - (91 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (9861861334613 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (9861861334613 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((91 / 400 : ℝ) - Real.pi * Real.exp (729 / 800 : ℝ)) := by
    rw [show (91 / 400 : ℝ) - Real.pi * Real.exp (729 / 800 : ℝ) =
      -(Real.pi * Real.exp (729 / 800 : ℝ) - (91 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (91 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (91 / 100 : ℝ)) := by
    have h := hpThetaJensenCell728_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (9861861334613 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell728_endpointUpper :
    hpThetaJensenKernelEndpointUpper (91 / 200 : ℝ) (729 / 1600 : ℝ) ≤ (2027024101 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (729 / 800 : ℝ)) (78144922936581319 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (729 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell728_product_upper
  have hD : (19525964838423 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (91 / 100 : ℝ) - (729 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell728_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell728_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (91 / 100 : ℝ) - (729 / 3200 : ℝ)) ≤
      (1 / (19525964838423 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (19525964838423 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((729 / 3200 : ℝ) - Real.pi * Real.exp (91 / 100 : ℝ)) ≤
      (2 / (19525964838423 / 10000000000 : ℝ) : ℝ) := by
    rw [show (729 / 3200 : ℝ) - Real.pi * Real.exp (91 / 100 : ℝ) =
      -(Real.pi * Real.exp (91 / 100 : ℝ) - (729 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (78144922936581319 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (78144922936581319 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell728_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (91 / 200 : ℝ) (729 / 1600 : ℝ)) :
    (399167521 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2027024101 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell728_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell728_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell729_leftExp :
    (24874298781 / 10000000000 : ℝ) ≤ Real.exp (729 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (729 / 800 : ℝ) (514442948019 / 500000000000 : ℝ)
    (24874298781 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell729_rightExp :
    Real.exp (73 / 80 : ℝ) ≤ (12452705549 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (73 / 80 : ℝ) (401924253 / 390625000 : ℝ)
    (12452705549 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell729_denomUpper :
    Real.exp (37982270083799557 / 5000000000000000 : ℝ) ≤ (19911228737921 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (37982270083799557 / 5000000000000000 : ℝ) (31698362167 /
    25000000000 : ℝ) (19911228737921 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell729_denomLower :
    (9855675075151 / 5000000000 : ℝ) ≤ Real.exp (9482956006999919 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9482956006999919 / 1250000000000000 : ℝ) (316883696339 /
    250000000000 : ℝ) (9855675075151 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell729_product_lower :
    (9768112256999919 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (729 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell729_leftExp
    (by norm_num : (0 : ℝ) ≤ (24874298781 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell729_product_upper :
    Real.pi * Real.exp (73 / 80 : ℝ) ≤ (39121332583799557 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell729_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell729_endpointLower :
    (1982580457 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (729 / 1600 : ℝ) (73 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9768112256999919 / 1250000000000000 : ℝ) (Real.pi * Real.exp (729 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell729_product_lower
  have hD : Real.exp (Real.pi * Real.exp (73 / 80 : ℝ) - (729 / 3200 : ℝ)) ≤
      (19911228737921 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell729_denomUpper
    linarith [hpThetaJensenCell729_product_upper]
  have hi : (1 / (19911228737921 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (73 / 80 : ℝ) - (729 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (19911228737921 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (19911228737921 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((729 / 3200 : ℝ) - Real.pi * Real.exp (73 / 80 : ℝ)) := by
    rw [show (729 / 3200 : ℝ) - Real.pi * Real.exp (73 / 80 : ℝ) =
      -(Real.pi * Real.exp (73 / 80 : ℝ) - (729 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (729 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (729 / 800 : ℝ)) := by
    have h := hpThetaJensenCell729_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (19911228737921 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell729_endpointUpper :
    hpThetaJensenKernelEndpointUpper (729 / 1600 : ℝ) (73 / 160 : ℝ) ≤ (2013583467 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (73 / 80 : ℝ)) (39121332583799557 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (73 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell729_product_upper
  have hD : (9855675075151 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (729 / 800 : ℝ) - (73 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell729_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell729_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (729 / 800 : ℝ) - (73 / 320 : ℝ)) ≤
      (1 / (9855675075151 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (9855675075151 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((73 / 320 : ℝ) - Real.pi * Real.exp (729 / 800 : ℝ)) ≤
      (2 / (9855675075151 / 5000000000 : ℝ) : ℝ) := by
    rw [show (73 / 320 : ℝ) - Real.pi * Real.exp (729 / 800 : ℝ) =
      -(Real.pi * Real.exp (729 / 800 : ℝ) - (73 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (39121332583799557 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (39121332583799557 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell729_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (729 / 1600 : ℝ) (73 / 160 : ℝ)) :
    (1982580457 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2013583467 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell729_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell729_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell730_leftExp :
    (3113176387 / 1250000000 : ℝ) ≤ Real.exp (73 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (73 / 80 : ℝ) (1028926087679 / 1000000000000 : ℝ)
    (3113176387 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell730_rightExp :
    Real.exp (731 / 800 : ℝ) ≤ (24936562327 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (731 / 800 : ℝ) (102896628089 / 100000000000 : ℝ)
    (24936562327 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell730_denomUpper :
    Real.exp (76059279650566911 / 10000000000000000 : ℝ) ≤ (10050381545511 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (76059279650566911 / 10000000000000000 : ℝ)
    (1268309928059 / 1000000000000 : ℝ) (10050381545511 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell730_denomLower :
    (19432361852 / 9765625 : ℝ) ≤ Real.exp (1186847894623513 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1186847894623513 / 156250000000000 : ℝ) (126790962387 /
    100000000000 : ℝ) (19432361852 / 9765625 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell730_product_lower :
    (1222541253998513 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (73 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell730_leftExp
    (by norm_num : (0 : ℝ) ≤ (3113176387 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell730_product_upper :
    Real.pi * Real.exp (731 / 800 : ℝ) ≤ (78340529650566911 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell730_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell730_endpointLower :
    (1969386387 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (73 / 160 : ℝ) (731 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1222541253998513 / 156250000000000 : ℝ) (Real.pi * Real.exp (73 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell730_product_lower
  have hD : Real.exp (Real.pi * Real.exp (731 / 800 : ℝ) - (73 / 320 : ℝ)) ≤
      (10050381545511 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell730_denomUpper
    linarith [hpThetaJensenCell730_product_upper]
  have hi : (1 / (10050381545511 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (731 / 800 : ℝ) - (73 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (10050381545511 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (10050381545511 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((73 / 320 : ℝ) - Real.pi * Real.exp (731 / 800 : ℝ)) := by
    rw [show (73 / 320 : ℝ) - Real.pi * Real.exp (731 / 800 : ℝ) =
      -(Real.pi * Real.exp (731 / 800 : ℝ) - (73 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (73 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (73 / 80 : ℝ)) := by
    have h := hpThetaJensenCell730_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (10050381545511 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell730_endpointUpper :
    hpThetaJensenKernelEndpointUpper (73 / 160 : ℝ) (731 / 1600 : ℝ) ≤ (1000103307 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (731 / 800 : ℝ)) (78340529650566911 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (731 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell730_product_upper
  have hD : (19432361852 / 9765625 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (73 / 80 : ℝ) - (731 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell730_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell730_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (73 / 80 : ℝ) - (731 / 3200 : ℝ)) ≤
      (1 / (19432361852 / 9765625 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (19432361852 / 9765625 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((731 / 3200 : ℝ) - Real.pi * Real.exp (73 / 80 : ℝ)) ≤
      (2 / (19432361852 / 9765625 : ℝ) : ℝ) := by
    rw [show (731 / 3200 : ℝ) - Real.pi * Real.exp (73 / 80 : ℝ) =
      -(Real.pi * Real.exp (73 / 80 : ℝ) - (731 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (78340529650566911 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (78340529650566911 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell730_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (73 / 160 : ℝ) (731 / 1600 : ℝ)) :
    (1969386387 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1000103307 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell730_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell730_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell731_leftExp :
    (12468281163 / 5000000000 : ℝ) ≤ Real.exp (731 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (731 / 800 : ℝ) (1028966280889 / 1000000000000 : ℝ)
    (12468281163 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell731_rightExp :
    Real.exp (183 / 200 : ℝ) ≤ (624193813 / 250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (183 / 200 : ℝ) (102900647567 / 100000000000 : ℝ)
    (624193813 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell731_denomUpper :
    Real.exp (1903853538564109 / 250000000000000 : ℝ) ≤ (4058470002251 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1903853538564109 / 250000000000000 : ℝ) (1268685965917 /
    1000000000000 : ℝ) (4058470002251 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell731_denomLower :
    (20088153939457 / 10000000000 : ℝ) ≤ Real.exp (4753312794428937 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4753312794428937 / 625000000000000 : ℝ) (79267816111 /
    62500000000 : ℝ) (20088153939457 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell731_product_lower :
    (4896281544428937 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (731 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell731_leftExp
    (by norm_num : (0 : ℝ) ≤ (12468281163 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell731_product_upper :
    Real.pi * Real.exp (183 / 200 : ℝ) ≤ (1960962913564109 / 250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell731_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell731_endpointLower :
    (24453191 / 125000000 : ℝ) ≤ hpThetaTraceEndpointLower (731 / 1600 : ℝ) (183 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4896281544428937 / 625000000000000 : ℝ) (Real.pi * Real.exp (731 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell731_product_lower
  have hD : Real.exp (Real.pi * Real.exp (183 / 200 : ℝ) - (731 / 3200 : ℝ)) ≤
      (4058470002251 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell731_denomUpper
    linarith [hpThetaJensenCell731_product_upper]
  have hi : (1 / (4058470002251 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (183 / 200 : ℝ) - (731 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4058470002251 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4058470002251 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((731 / 3200 : ℝ) - Real.pi * Real.exp (183 / 200 : ℝ)) := by
    rw [show (731 / 3200 : ℝ) - Real.pi * Real.exp (183 / 200 : ℝ) =
      -(Real.pi * Real.exp (183 / 200 : ℝ) - (731 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (731 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (731 / 800 : ℝ)) := by
    have h := hpThetaJensenCell731_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4058470002251 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell731_endpointUpper :
    hpThetaJensenKernelEndpointUpper (731 / 1600 : ℝ) (183 / 400 : ℝ) ≤ (1986893427 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (183 / 200 : ℝ)) (1960962913564109 / 250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (183 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell731_product_upper
  have hD : (20088153939457 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (731 / 800 : ℝ) - (183 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell731_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell731_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (731 / 800 : ℝ) - (183 / 800 : ℝ)) ≤
      (1 / (20088153939457 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (20088153939457 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((183 / 800 : ℝ) - Real.pi * Real.exp (731 / 800 : ℝ)) ≤
      (2 / (20088153939457 / 10000000000 : ℝ) : ℝ) := by
    rw [show (183 / 800 : ℝ) - Real.pi * Real.exp (731 / 800 : ℝ) =
      -(Real.pi * Real.exp (731 / 800 : ℝ) - (183 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1960962913564109 / 250000000000000 : ℝ) ^ 2 - 6 *
      (1960962913564109 / 250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell731_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (731 / 1600 : ℝ) (183 / 400 : ℝ)) :
    (24453191 / 125000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1986893427 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell731_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell731_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell732_leftExp :
    (12483876259 / 5000000000 : ℝ) ≤ Real.exp (183 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (183 / 200 : ℝ) (1029006475669 / 1000000000000 : ℝ)
    (12483876259 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell732_rightExp :
    Real.exp (733 / 800 : ℝ) ≤ (999959269 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (733 / 800 : ℝ) (1029046672021 / 1000000000000 : ℝ)
    (999959269 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell732_denomUpper :
    Real.exp (3049965039775517 / 400000000000000 : ℝ) ≤ (20486014083179 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3049965039775517 / 400000000000000 : ℝ) (253812520263 /
    200000000000 : ℝ) (20486014083179 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell732_denomLower :
    (5069905152013 / 2500000000 : ℝ) ≤ Real.exp (4759241660533041 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4759241660533041 / 625000000000000 : ℝ) (317165272031 /
    250000000000 : ℝ) (5069905152013 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell732_product_lower :
    (4902405723033041 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (183 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell732_leftExp
    (by norm_num : (0 : ℝ) ≤ (12483876259 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell732_product_upper :
    Real.pi * Real.exp (733 / 800 : ℝ) ≤ (3141465039775517 / 400000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell732_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell732_endpointLower :
    (1943187021 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (183 / 400 : ℝ) (733 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4902405723033041 / 625000000000000 : ℝ) (Real.pi * Real.exp (183 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell732_product_lower
  have hD : Real.exp (Real.pi * Real.exp (733 / 800 : ℝ) - (183 / 800 : ℝ)) ≤
      (20486014083179 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell732_denomUpper
    linarith [hpThetaJensenCell732_product_upper]
  have hi : (1 / (20486014083179 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (733 / 800 : ℝ) - (183 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (20486014083179 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (20486014083179 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((183 / 800 : ℝ) - Real.pi * Real.exp (733 / 800 : ℝ)) := by
    rw [show (183 / 800 : ℝ) - Real.pi * Real.exp (733 / 800 : ℝ) =
      -(Real.pi * Real.exp (733 / 800 : ℝ) - (183 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (183 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (183 / 200 : ℝ)) := by
    have h := hpThetaJensenCell732_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (20486014083179 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell732_endpointUpper :
    hpThetaJensenKernelEndpointUpper (183 / 400 : ℝ) (733 / 1600 : ℝ) ≤ (1973643791 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (733 / 800 : ℝ)) (3141465039775517 / 400000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (733 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell732_product_upper
  have hD : (5069905152013 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (183 / 200 : ℝ) - (733 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell732_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell732_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (183 / 200 : ℝ) - (733 / 3200 : ℝ)) ≤
      (1 / (5069905152013 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5069905152013 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((733 / 3200 : ℝ) - Real.pi * Real.exp (183 / 200 : ℝ)) ≤
      (2 / (5069905152013 / 2500000000 : ℝ) : ℝ) := by
    rw [show (733 / 3200 : ℝ) - Real.pi * Real.exp (183 / 200 : ℝ) =
      -(Real.pi * Real.exp (183 / 200 : ℝ) - (733 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (3141465039775517 / 400000000000000 : ℝ) ^ 2 - 6 *
      (3141465039775517 / 400000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell732_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (183 / 400 : ℝ) (733 / 1600 : ℝ)) :
    (1943187021 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1973643791 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell732_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell732_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell733_leftExp :
    (24998981723 / 10000000000 : ℝ) ≤ Real.exp (733 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (733 / 800 : ℝ) (51452333601 / 50000000000 : ℝ)
    (24998981723 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell733_rightExp :
    Real.exp (367 / 400 : ℝ) ≤ (25030249991 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (367 / 400 : ℝ) (514543434971 / 500000000000 : ℝ)
    (25030249991 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell733_denomUpper :
    Real.exp (76344233159975663 / 10000000000000000 : ℝ) ≤ (10340890109421 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (76344233159975663 / 10000000000000000 : ℝ) (126943983533
    / 100000000000 : ℝ) (10340890109421 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell733_denomLower :
    (10236581565053 / 5000000000 : ℝ) ≤ Real.exp (9530356373640377 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9530356373640377 / 1250000000000000 : ℝ) (317259429003 /
    250000000000 : ℝ) (10236581565053 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell733_product_lower :
    (9817075123640377 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (733 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell733_leftExp
    (by norm_num : (0 : ℝ) ≤ (24998981723 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell733_product_upper :
    Real.pi * Real.exp (367 / 400 : ℝ) ≤ (78634858159975663 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell733_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell733_endpointLower :
    (1930181493 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (733 / 1600 : ℝ) (367 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9817075123640377 / 1250000000000000 : ℝ) (Real.pi * Real.exp (733 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell733_product_lower
  have hD : Real.exp (Real.pi * Real.exp (367 / 400 : ℝ) - (733 / 3200 : ℝ)) ≤
      (10340890109421 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell733_denomUpper
    linarith [hpThetaJensenCell733_product_upper]
  have hi : (1 / (10340890109421 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (367 / 400 : ℝ) - (733 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (10340890109421 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (10340890109421 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((733 / 3200 : ℝ) - Real.pi * Real.exp (367 / 400 : ℝ)) := by
    rw [show (733 / 3200 : ℝ) - Real.pi * Real.exp (367 / 400 : ℝ) =
      -(Real.pi * Real.exp (367 / 400 : ℝ) - (733 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (733 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (733 / 800 : ℝ)) := by
    have h := hpThetaJensenCell733_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (10340890109421 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell733_endpointUpper :
    hpThetaJensenKernelEndpointUpper (733 / 1600 : ℝ) (367 / 800 : ℝ) ≤ (196045759 / 1000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (367 / 400 : ℝ)) (78634858159975663 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (367 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell733_product_upper
  have hD : (10236581565053 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (733 / 800 : ℝ) - (367 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell733_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell733_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (733 / 800 : ℝ) - (367 / 1600 : ℝ)) ≤
      (1 / (10236581565053 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (10236581565053 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((367 / 1600 : ℝ) - Real.pi * Real.exp (733 / 800 : ℝ)) ≤
      (2 / (10236581565053 / 5000000000 : ℝ) : ℝ) := by
    rw [show (367 / 1600 : ℝ) - Real.pi * Real.exp (733 / 800 : ℝ) =
      -(Real.pi * Real.exp (733 / 800 : ℝ) - (367 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (78634858159975663 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (78634858159975663 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell733_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (733 / 1600 : ℝ) (367 / 800 : ℝ)) :
    (1930181493 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (196045759 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell733_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell733_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell734_leftExp :
    (25030249989 / 10000000000 : ℝ) ≤ Real.exp (367 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (367 / 400 : ℝ) (1029086869941 / 1000000000000 : ℝ)
    (25030249989 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell734_rightExp :
    Real.exp (147 / 160 : ℝ) ≤ (12530778683 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (147 / 160 : ℝ) (1029127069433 / 1000000000000 : ℝ)
    (12530778683 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell734_denomUpper :
    Real.exp (38219731595062019 / 5000000000000000 : ℝ) ≤ (5219918412097 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (38219731595062019 / 5000000000000000 : ℝ) (317454417257
    / 250000000000 : ℝ) (5219918412097 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell734_denomLower :
    (20668806396989 / 10000000000 : ℝ) ≤ Real.exp (9542244765430311 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9542244765430311 / 1250000000000000 : ℝ) (1269414942507
    / 1000000000000 : ℝ) (20668806396989 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell734_product_lower :
    (9829354140430311 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (367 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell734_leftExp
    (by norm_num : (0 : ℝ) ≤ (25030249989 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell734_product_upper :
    Real.pi * Real.exp (147 / 160 : ℝ) ≤ (39366606595062019 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell734_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell734_endpointLower :
    (95861929 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (367 / 800 : ℝ) (147 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9829354140430311 / 1250000000000000 : ℝ) (Real.pi * Real.exp (367 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell734_product_lower
  have hD : Real.exp (Real.pi * Real.exp (147 / 160 : ℝ) - (367 / 1600 : ℝ)) ≤
      (5219918412097 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell734_denomUpper
    linarith [hpThetaJensenCell734_product_upper]
  have hi : (1 / (5219918412097 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (147 / 160 : ℝ) - (367 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5219918412097 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5219918412097 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((367 / 1600 : ℝ) - Real.pi * Real.exp (147 / 160 : ℝ)) := by
    rw [show (367 / 1600 : ℝ) - Real.pi * Real.exp (147 / 160 : ℝ) =
      -(Real.pi * Real.exp (147 / 160 : ℝ) - (367 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (367 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (367 / 400 : ℝ)) := by
    have h := hpThetaJensenCell734_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5219918412097 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell734_endpointUpper :
    hpThetaJensenKernelEndpointUpper (367 / 800 : ℝ) (147 / 320 : ℝ) ≤ (121708419 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (147 / 160 : ℝ)) (39366606595062019 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (147 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell734_product_upper
  have hD : (20668806396989 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (367 / 400 : ℝ) - (147 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell734_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell734_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (367 / 400 : ℝ) - (147 / 640 : ℝ)) ≤
      (1 / (20668806396989 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (20668806396989 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((147 / 640 : ℝ) - Real.pi * Real.exp (367 / 400 : ℝ)) ≤
      (2 / (20668806396989 / 10000000000 : ℝ) : ℝ) := by
    rw [show (147 / 640 : ℝ) - Real.pi * Real.exp (367 / 400 : ℝ) =
      -(Real.pi * Real.exp (367 / 400 : ℝ) - (147 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (39366606595062019 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (39366606595062019 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell734_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (367 / 800 : ℝ) (147 / 320 : ℝ)) :
    (95861929 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (121708419 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell734_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell734_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell735_leftExp :
    (5012311473 / 2000000000 : ℝ) ≤ Real.exp (147 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (147 / 160 : ℝ) (128640883679 / 125000000000 : ℝ)
    (5012311473 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell735_rightExp :
    Real.exp (23 / 25 : ℝ) ≤ (250929039 / 100000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (23 / 25 : ℝ) (514583635247 / 500000000000 : ℝ)
    (250929039 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell735_denomUpper :
    Real.exp (765348162419127 / 100000000000000 : ℝ) ≤ (131748249653 / 62500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (765348162419127 / 100000000000000 : ℝ) (635098051751 /
    500000000000 : ℝ) (131748249653 / 62500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell735_denomLower :
    (20866575627769 / 10000000000 : ℝ) ≤ Real.exp (1910829703135627 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1910829703135627 / 250000000000000 : ℝ) (317448192171 /
    250000000000 : ℝ) (20866575627769 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell735_product_lower :
    (1968329703135627 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (147 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell735_leftExp
    (by norm_num : (0 : ℝ) ≤ (5012311473 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell735_product_upper :
    Real.pi * Real.exp (23 / 25 : ℝ) ≤ (788316912419127 / 100000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell735_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell735_endpointLower :
    (1904358161 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (147 / 320 : ℝ) (23 / 50 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1968329703135627 / 250000000000000 : ℝ) (Real.pi * Real.exp (147 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell735_product_lower
  have hD : Real.exp (Real.pi * Real.exp (23 / 25 : ℝ) - (147 / 640 : ℝ)) ≤
      (131748249653 / 62500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell735_denomUpper
    linarith [hpThetaJensenCell735_product_upper]
  have hi : (1 / (131748249653 / 62500000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (23 / 25 : ℝ) - (147 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (131748249653 / 62500000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (131748249653 / 62500000 : ℝ) : ℝ) ≤
      2 * Real.exp ((147 / 640 : ℝ) - Real.pi * Real.exp (23 / 25 : ℝ)) := by
    rw [show (147 / 640 : ℝ) - Real.pi * Real.exp (23 / 25 : ℝ) =
      -(Real.pi * Real.exp (23 / 25 : ℝ) - (147 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (147 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (147 / 160 : ℝ)) := by
    have h := hpThetaJensenCell735_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (131748249653 / 62500000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell735_endpointUpper :
    hpThetaJensenKernelEndpointUpper (147 / 320 : ℝ) (23 / 50 : ℝ) ≤ (386855003 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (23 / 25 : ℝ)) (788316912419127 / 100000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (23 / 50 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell735_product_upper
  have hD : (20866575627769 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (147 / 160 : ℝ) - (23 / 100 : ℝ)) := by
    apply le_trans hpThetaJensenCell735_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell735_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (147 / 160 : ℝ) - (23 / 100 : ℝ)) ≤
      (1 / (20866575627769 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (20866575627769 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((23 / 100 : ℝ) - Real.pi * Real.exp (147 / 160 : ℝ)) ≤
      (2 / (20866575627769 / 10000000000 : ℝ) : ℝ) := by
    rw [show (23 / 100 : ℝ) - Real.pi * Real.exp (147 / 160 : ℝ) =
      -(Real.pi * Real.exp (147 / 160 : ℝ) - (23 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (788316912419127 / 100000000000000 : ℝ) ^ 2 - 6 *
      (788316912419127 / 100000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell735_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (147 / 320 : ℝ) (23 / 50 : ℝ)) :
    (1904358161 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (386855003 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell735_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell735_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell736_leftExp :
    (25092903899 / 10000000000 : ℝ) ≤ Real.exp (23 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (23 / 25 : ℝ) (1029167270493 / 1000000000000 : ℝ)
    (25092903899 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell736_rightExp :
    Real.exp (737 / 800 : ℝ) ≤ (12562144821 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (737 / 800 : ℝ) (514603736563 / 500000000000 : ℝ)
    (12562144821 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell736_denomUpper :
    Real.exp (38315146234639853 / 5000000000000000 : ℝ) ≤ (2660243125761 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (38315146234639853 / 5000000000000000 : ℝ) (158821892479
    / 125000000000 : ℝ) (2660243125761 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell736_denomLower :
    (10533248183239 / 5000000000 : ℝ) ≤ Real.exp (9566067643233401 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9566067643233401 / 1250000000000000 : ℝ) (317542798903 /
    250000000000 : ℝ) (10533248183239 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell736_product_lower :
    (9853958268233401 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (23 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell736_leftExp
    (by norm_num : (0 : ℝ) ≤ (25092903899 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell736_product_upper :
    Real.pi * Real.exp (737 / 800 : ℝ) ≤ (39465146234639853 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell736_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell736_endpointLower :
    (1891540117 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (23 / 50 : ℝ) (737 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9853958268233401 / 1250000000000000 : ℝ) (Real.pi * Real.exp (23 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell736_product_lower
  have hD : Real.exp (Real.pi * Real.exp (737 / 800 : ℝ) - (23 / 100 : ℝ)) ≤
      (2660243125761 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell736_denomUpper
    linarith [hpThetaJensenCell736_product_upper]
  have hi : (1 / (2660243125761 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (737 / 800 : ℝ) - (23 / 100 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2660243125761 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2660243125761 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((23 / 100 : ℝ) - Real.pi * Real.exp (737 / 800 : ℝ)) := by
    rw [show (23 / 100 : ℝ) - Real.pi * Real.exp (737 / 800 : ℝ) =
      -(Real.pi * Real.exp (737 / 800 : ℝ) - (23 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (23 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (23 / 25 : ℝ)) := by
    have h := hpThetaJensenCell736_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2660243125761 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell736_endpointUpper :
    hpThetaJensenKernelEndpointUpper (23 / 50 : ℝ) (737 / 1600 : ℝ) ≤ (1921278403 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (737 / 800 : ℝ)) (39465146234639853 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (737 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell736_product_upper
  have hD : (10533248183239 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (23 / 25 : ℝ) - (737 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell736_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell736_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (23 / 25 : ℝ) - (737 / 3200 : ℝ)) ≤
      (1 / (10533248183239 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (10533248183239 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((737 / 3200 : ℝ) - Real.pi * Real.exp (23 / 25 : ℝ)) ≤
      (2 / (10533248183239 / 5000000000 : ℝ) : ℝ) := by
    rw [show (737 / 3200 : ℝ) - Real.pi * Real.exp (23 / 25 : ℝ) =
      -(Real.pi * Real.exp (23 / 25 : ℝ) - (737 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (39465146234639853 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (39465146234639853 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell736_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (23 / 50 : ℝ) (737 / 1600 : ℝ)) :
    (1891540117 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1921278403 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell736_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell736_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell737_leftExp :
    (25124289641 / 10000000000 : ℝ) ≤ Real.exp (737 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (737 / 800 : ℝ) (1646731957 / 1600000000 : ℝ)
    (25124289641 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell737_rightExp :
    Real.exp (369 / 400 : ℝ) ≤ (25155714641 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (369 / 400 : ℝ) (64327979833 / 62500000000 : ℝ)
    (25155714641 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell737_denomUpper :
    Real.exp (76725892026163113 / 10000000000000000 : ℝ) ≤ (10743187535733 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (76725892026163113 / 10000000000000000 : ℝ)
    (1270954779101 / 1000000000000 : ℝ) (10743187535733 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell737_denomLower :
    (21268594503137 / 10000000000 : ℝ) ≤ Real.exp (9578002167731059 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9578002167731059 / 1250000000000000 : ℝ) (254110044877 /
    200000000000 : ℝ) (21268594503137 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell737_product_lower :
    (9866283417731059 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (737 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell737_leftExp
    (by norm_num : (0 : ℝ) ≤ (25124289641 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell737_product_upper :
    Real.pi * Real.exp (369 / 400 : ℝ) ≤ (79029017026163113 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell737_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell737_endpointLower :
    (1878784327 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (737 / 1600 : ℝ) (369 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9866283417731059 / 1250000000000000 : ℝ) (Real.pi * Real.exp (737 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell737_product_lower
  have hD : Real.exp (Real.pi * Real.exp (369 / 400 : ℝ) - (737 / 3200 : ℝ)) ≤
      (10743187535733 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell737_denomUpper
    linarith [hpThetaJensenCell737_product_upper]
  have hi : (1 / (10743187535733 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (369 / 400 : ℝ) - (737 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (10743187535733 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (10743187535733 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((737 / 3200 : ℝ) - Real.pi * Real.exp (369 / 400 : ℝ)) := by
    rw [show (737 / 3200 : ℝ) - Real.pi * Real.exp (369 / 400 : ℝ) =
      -(Real.pi * Real.exp (369 / 400 : ℝ) - (737 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (737 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (737 / 800 : ℝ)) := by
    have h := hpThetaJensenCell737_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (10743187535733 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell737_endpointUpper :
    hpThetaJensenKernelEndpointUpper (737 / 1600 : ℝ) (369 / 800 : ℝ) ≤ (477086187 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (369 / 400 : ℝ)) (79029017026163113 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (369 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell737_product_upper
  have hD : (21268594503137 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (737 / 800 : ℝ) - (369 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell737_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell737_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (737 / 800 : ℝ) - (369 / 1600 : ℝ)) ≤
      (1 / (21268594503137 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (21268594503137 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((369 / 1600 : ℝ) - Real.pi * Real.exp (737 / 800 : ℝ)) ≤
      (2 / (21268594503137 / 10000000000 : ℝ) : ℝ) := by
    rw [show (369 / 1600 : ℝ) - Real.pi * Real.exp (737 / 800 : ℝ) =
      -(Real.pi * Real.exp (737 / 800 : ℝ) - (369 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (79029017026163113 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (79029017026163113 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell737_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (737 / 1600 : ℝ) (369 / 800 : ℝ)) :
    (1878784327 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (477086187 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell737_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell737_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell738_leftExp :
    (25155714639 / 10000000000 : ℝ) ≤ Real.exp (369 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (369 / 400 : ℝ) (1029247677327 / 1000000000000 : ℝ)
    (25155714639 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell738_rightExp :
    Real.exp (739 / 800 : ℝ) ≤ (5037435789 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (739 / 800 : ℝ) (10292878831 / 10000000000 : ℝ)
    (5037435789 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell738_denomUpper :
    Real.exp (15364323012671877 / 2000000000000000 : ℝ) ≤ (21693036715297 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (15364323012671877 / 2000000000000000 : ℝ) (1271335022381
    / 1000000000000 : ℝ) (21693036715297 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell738_denomLower :
    (21472896251977 / 10000000000 : ℝ) ≤ Real.exp (9589952108020661 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9589952108020661 / 1250000000000000 : ℝ) (158866232009 /
    125000000000 : ℝ) (21472896251977 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell738_product_lower :
    (9878623983020661 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (369 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell738_leftExp
    (by norm_num : (0 : ℝ) ≤ (25155714639 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell738_product_upper :
    Real.pi * Real.exp (739 / 800 : ℝ) ≤ (15825573012671877 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell738_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell738_endpointLower :
    (1866090669 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (369 / 800 : ℝ) (739 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9878623983020661 / 1250000000000000 : ℝ) (Real.pi * Real.exp (369 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell738_product_lower
  have hD : Real.exp (Real.pi * Real.exp (739 / 800 : ℝ) - (369 / 1600 : ℝ)) ≤
      (21693036715297 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell738_denomUpper
    linarith [hpThetaJensenCell738_product_upper]
  have hi : (1 / (21693036715297 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (739 / 800 : ℝ) - (369 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (21693036715297 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (21693036715297 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((369 / 1600 : ℝ) - Real.pi * Real.exp (739 / 800 : ℝ)) := by
    rw [show (369 / 1600 : ℝ) - Real.pi * Real.exp (739 / 800 : ℝ) =
      -(Real.pi * Real.exp (739 / 800 : ℝ) - (369 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (369 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (369 / 400 : ℝ)) := by
    have h := hpThetaJensenCell738_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (21693036715297 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell738_endpointUpper :
    hpThetaJensenKernelEndpointUpper (369 / 800 : ℝ) (739 / 1600 : ℝ) ≤ (947736963 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (739 / 800 : ℝ)) (15825573012671877 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (739 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell738_product_upper
  have hD : (21472896251977 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (369 / 400 : ℝ) - (739 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell738_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell738_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (369 / 400 : ℝ) - (739 / 3200 : ℝ)) ≤
      (1 / (21472896251977 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (21472896251977 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((739 / 3200 : ℝ) - Real.pi * Real.exp (369 / 400 : ℝ)) ≤
      (2 / (21472896251977 / 10000000000 : ℝ) : ℝ) := by
    rw [show (739 / 3200 : ℝ) - Real.pi * Real.exp (369 / 400 : ℝ) =
      -(Real.pi * Real.exp (369 / 400 : ℝ) - (739 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (15825573012671877 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (15825573012671877 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell738_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (369 / 800 : ℝ) (739 / 1600 : ℝ)) :
    (1866090669 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (947736963 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell738_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell738_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell739_leftExp :
    (25187178943 / 10000000000 : ℝ) ≤ Real.exp (739 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (739 / 800 : ℝ) (1029287883099 / 1000000000000 : ℝ)
    (25187178943 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell739_rightExp :
    Real.exp (37 / 40 : ℝ) ≤ (5043736521 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (37 / 40 : ℝ) (257332022611 / 250000000000 : ℝ)
    (5043736521 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell739_denomUpper :
    Real.exp (15383492348217953 / 2000000000000000 : ℝ) ≤ (4380391376259 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (15383492348217953 / 2000000000000000 : ℝ) (19870560481 /
    15625000000 : ℝ) (4380391376259 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell739_denomLower :
    (2167942818499 / 1000000000 : ℝ) ≤ Real.exp (9601917483737157 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9601917483737157 / 1250000000000000 : ℝ) (1271310091771
    / 1000000000000 : ℝ) (2167942818499 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell739_product_lower :
    (9890979983737157 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (739 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell739_leftExp
    (by norm_num : (0 : ℝ) ≤ (25187178943 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell739_product_upper :
    Real.pi * Real.exp (37 / 40 : ℝ) ≤ (15845367348217953 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell739_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell739_endpointLower :
    (92672951 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (739 / 1600 : ℝ) (37 / 80 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9890979983737157 / 1250000000000000 : ℝ) (Real.pi * Real.exp (739 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell739_product_lower
  have hD : Real.exp (Real.pi * Real.exp (37 / 40 : ℝ) - (739 / 3200 : ℝ)) ≤
      (4380391376259 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell739_denomUpper
    linarith [hpThetaJensenCell739_product_upper]
  have hi : (1 / (4380391376259 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (37 / 40 : ℝ) - (739 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4380391376259 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4380391376259 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((739 / 3200 : ℝ) - Real.pi * Real.exp (37 / 40 : ℝ)) := by
    rw [show (739 / 3200 : ℝ) - Real.pi * Real.exp (37 / 40 : ℝ) =
      -(Real.pi * Real.exp (37 / 40 : ℝ) - (739 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (739 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (739 / 800 : ℝ)) := by
    have h := hpThetaJensenCell739_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4380391376259 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell739_endpointUpper :
    hpThetaJensenKernelEndpointUpper (739 / 1600 : ℝ) (37 / 80 : ℝ) ≤ (941332907 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (37 / 40 : ℝ)) (15845367348217953 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (37 / 80 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell739_product_upper
  have hD : (2167942818499 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (739 / 800 : ℝ) - (37 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell739_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell739_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (739 / 800 : ℝ) - (37 / 160 : ℝ)) ≤
      (1 / (2167942818499 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2167942818499 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((37 / 160 : ℝ) - Real.pi * Real.exp (739 / 800 : ℝ)) ≤
      (2 / (2167942818499 / 1000000000 : ℝ) : ℝ) := by
    rw [show (37 / 160 : ℝ) - Real.pi * Real.exp (739 / 800 : ℝ) =
      -(Real.pi * Real.exp (739 / 800 : ℝ) - (37 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (15845367348217953 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (15845367348217953 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell739_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (739 / 1600 : ℝ) (37 / 80 : ℝ)) :
    (92672951 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (941332907 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell739_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell739_endpointUpper

def hpThetaJensenCellsBatch036Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (420835791 / 2000000000 : ℝ)
  | 1 => (2090413199 / 10000000000 : ℝ)
  | 2 => (519177849 / 2500000000 : ℝ)
  | 3 => (12894209 / 62500000 : ℝ)
  | 4 => (81979969 / 400000000 : ℝ)
  | 5 => (508997161 / 2500000000 : ℝ)
  | 6 => (2022541587 / 10000000000 : ℝ)
  | 7 => (251144743 / 1250000000 : ℝ)
  | 8 => (399167521 / 2000000000 : ℝ)
  | 9 => (1982580457 / 10000000000 : ℝ)
  | 10 => (1969386387 / 10000000000 : ℝ)
  | 11 => (24453191 / 125000000 : ℝ)
  | 12 => (1943187021 / 10000000000 : ℝ)
  | 13 => (1930181493 / 10000000000 : ℝ)
  | 14 => (95861929 / 500000000 : ℝ)
  | 15 => (1904358161 / 10000000000 : ℝ)
  | 16 => (1891540117 / 10000000000 : ℝ)
  | 17 => (1878784327 / 10000000000 : ℝ)
  | 18 => (1866090669 / 10000000000 : ℝ)
  | 19 => (92672951 / 500000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch036Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (267107333 / 1250000000 : ℝ)
  | 1 => (424580759 / 2000000000 : ℝ)
  | 2 => (2109013581 / 10000000000 : ℝ)
  | 3 => (1047593959 / 5000000000 : ℝ)
  | 4 => (2081426699 / 10000000000 : ℝ)
  | 5 => (1033864909 / 5000000000 : ℝ)
  | 6 => (513524291 / 2500000000 : ℝ)
  | 7 => (2040528629 / 10000000000 : ℝ)
  | 8 => (2027024101 / 10000000000 : ℝ)
  | 9 => (2013583467 / 10000000000 : ℝ)
  | 10 => (1000103307 / 5000000000 : ℝ)
  | 11 => (1986893427 / 10000000000 : ℝ)
  | 12 => (1973643791 / 10000000000 : ℝ)
  | 13 => (196045759 / 1000000000 : ℝ)
  | 14 => (121708419 / 625000000 : ℝ)
  | 15 => (386855003 / 2000000000 : ℝ)
  | 16 => (1921278403 / 10000000000 : ℝ)
  | 17 => (477086187 / 2500000000 : ℝ)
  | 18 => (947736963 / 5000000000 : ℝ)
  | 19 => (941332907 / 5000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch036_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((720 : ℝ) + (j.val : ℝ)) / 1600)
      (((720 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch036Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch036Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell720_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell721_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell722_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell723_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell724_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell725_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell726_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell727_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell728_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell729_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell730_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell731_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell732_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell733_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell734_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell735_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell736_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell737_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell738_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell739_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper] at h ⊢
    exact h

end HodgeProofHP
