import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1360_leftExp :
    (54739473917 / 10000000000 : ℝ) ≤ Real.exp (17 / 10 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (17 / 10 : ℝ) (1054561457063 / 1000000000000 : ℝ)
    (54739473917 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1360_rightExp :
    Real.exp (1361 / 800 : ℝ) ≤ (13701985261 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1361 / 800 : ℝ) (42184106067 / 40000000000 : ℝ)
    (13701985261 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1360_denomUpper :
    Real.exp (41983560982060773 / 2500000000000000 : ℝ) ≤ (98233937098808733 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (41983560982060773 / 2500000000000000 : ℝ) (67604460621 /
    40000000000 : ℝ) (98233937098808733 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1360_denomLower :
    (192225924270267097 / 10000000000 : ℝ) ≤ Real.exp (20964496042731983 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (20964496042731983 / 1250000000000000 : ℝ) (1688959064611
    / 1000000000000 : ℝ) (192225924270267097 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1360_product_lower :
    (21496136667731983 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (17 / 10 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1360_leftExp
    (by norm_num : (0 : ℝ) ≤ (54739473917 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1360_product_upper :
    Real.pi * Real.exp (1361 / 800 : ℝ) ≤ (43046060982060773 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1360_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1360_endpointLower :
    (219833 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (17 / 20 : ℝ) (1361 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (21496136667731983 / 1250000000000000 : ℝ) (Real.pi * Real.exp (17 / 10 : ℝ))
    (by norm_num) hpThetaJensenCell1360_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1361 / 800 : ℝ) - (17 / 40 : ℝ)) ≤
      (98233937098808733 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1360_denomUpper
    linarith [hpThetaJensenCell1360_product_upper]
  have hi : (1 / (98233937098808733 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1361 / 800 : ℝ) - (17 / 40 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (98233937098808733 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (98233937098808733 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((17 / 40 : ℝ) - Real.pi * Real.exp (1361 / 800 : ℝ)) := by
    rw [show (17 / 40 : ℝ) - Real.pi * Real.exp (1361 / 800 : ℝ) =
      -(Real.pi * Real.exp (1361 / 800 : ℝ) - (17 / 40 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (17 / 10 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (17 / 10 : ℝ)) := by
    have h := hpThetaJensenCell1360_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (98233937098808733 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1360_endpointUpper :
    hpThetaJensenKernelEndpointUpper (17 / 20 : ℝ) (1361 / 1600 : ℝ) ≤ (225867 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1361 / 800 : ℝ)) (43046060982060773 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1361 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1360_product_upper
  have hD : (192225924270267097 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (17 / 10 : ℝ) - (1361 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1360_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1360_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (17 / 10 : ℝ) - (1361 / 3200 : ℝ)) ≤
      (1 / (192225924270267097 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (192225924270267097 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1361 / 3200 : ℝ) - Real.pi * Real.exp (17 / 10 : ℝ)) ≤
      (2 / (192225924270267097 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1361 / 3200 : ℝ) - Real.pi * Real.exp (17 / 10 : ℝ) =
      -(Real.pi * Real.exp (17 / 10 : ℝ) - (1361 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (43046060982060773 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (43046060982060773 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1360_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (17 / 20 : ℝ) (1361 / 1600 : ℝ)) :
    (219833 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (225867 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1360_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1360_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1361_leftExp :
    (54807941041 / 10000000000 : ℝ) ≤ Real.exp (1361 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1361 / 800 : ℝ) (527301325837 / 500000000000 : ℝ)
    (54807941041 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1361_rightExp :
    Real.exp (681 / 400 : ℝ) ≤ (54876493807 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (681 / 400 : ℝ) (131830480987 / 125000000000 : ℝ)
    (54876493807 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1361_denomUpper :
    Real.exp (168146483808614551 / 10000000000000000 : ℝ) ≤ (50170567741609003 / 2500000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (168146483808614551 / 10000000000000000 : ℝ)
    (1691232853179 / 1000000000000 : ℝ) (50170567741609003 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1361_denomLower :
    (196344043827193307 / 10000000000 : ℝ) ≤ Real.exp (20990992388859659 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (20990992388859659 / 1250000000000000 : ℝ) (845039108169
    / 500000000000 : ℝ) (196344043827193307 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1361_product_lower :
    (21523023638859659 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1361 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1361_leftExp
    (by norm_num : (0 : ℝ) ≤ (54807941041 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1361_product_upper :
    Real.pi * Real.exp (681 / 400 : ℝ) ≤ (172399608808614551 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1361_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1361_endpointLower :
    (134863 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (1361 / 1600 : ℝ) (681 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (21523023638859659 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1361 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1361_product_lower
  have hD : Real.exp (Real.pi * Real.exp (681 / 400 : ℝ) - (1361 / 3200 : ℝ)) ≤
      (50170567741609003 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1361_denomUpper
    linarith [hpThetaJensenCell1361_product_upper]
  have hi : (1 / (50170567741609003 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (681 / 400 : ℝ) - (1361 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (50170567741609003 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (50170567741609003 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1361 / 3200 : ℝ) - Real.pi * Real.exp (681 / 400 : ℝ)) := by
    rw [show (1361 / 3200 : ℝ) - Real.pi * Real.exp (681 / 400 : ℝ) =
      -(Real.pi * Real.exp (681 / 400 : ℝ) - (1361 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1361 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1361 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1361_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (50170567741609003 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1361_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1361 / 1600 : ℝ) (681 / 800 : ℝ) ≤ (277137 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (681 / 400 : ℝ)) (172399608808614551 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (681 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1361_product_upper
  have hD : (196344043827193307 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1361 / 800 : ℝ) - (681 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1361_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1361_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1361 / 800 : ℝ) - (681 / 1600 : ℝ)) ≤
      (1 / (196344043827193307 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (196344043827193307 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((681 / 1600 : ℝ) - Real.pi * Real.exp (1361 / 800 : ℝ)) ≤
      (2 / (196344043827193307 / 10000000000 : ℝ) : ℝ) := by
    rw [show (681 / 1600 : ℝ) - Real.pi * Real.exp (1361 / 800 : ℝ) =
      -(Real.pi * Real.exp (1361 / 800 : ℝ) - (681 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (172399608808614551 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (172399608808614551 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1361_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1361 / 1600 : ℝ) (681 / 800 : ℝ)) :
    (134863 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (277137 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1361_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1361_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1362_leftExp :
    (10975298761 / 2000000000 : ℝ) ≤ Real.exp (681 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (681 / 400 : ℝ) (210928769579 / 200000000000 : ℝ)
    (10975298761 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1362_rightExp :
    Real.exp (1363 / 800 : ℝ) ≤ (10989026463 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1363 / 800 : ℝ) (527342522863 / 500000000000 : ℝ)
    (10989026463 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1362_denomUpper :
    Real.exp (33671798612975559 / 2000000000000000 : ℝ) ≤ (204992591925103587 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (33671798612975559 / 2000000000000000 : ℝ) (169235635943
    / 100000000000 : ℝ) (204992591925103587 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1362_denomLower :
    (200555783016371081 / 10000000000 : ℝ) ≤ Real.exp (4203504473145939 / 250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (4203504473145939 / 250000000000000 : ℝ) (52849985361 /
    31250000000 : ℝ) (200555783016371081 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1362_product_lower :
    (4309988848145939 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (681 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1362_leftExp
    (by norm_num : (0 : ℝ) ≤ (10975298761 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1362_product_upper :
    Real.pi * Real.exp (1363 / 800 : ℝ) ≤ (34523048612975559 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1362_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1362_endpointLower :
    (1058989 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (681 / 800 : ℝ) (1363 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4309988848145939 / 250000000000000 : ℝ) (Real.pi * Real.exp (681 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1362_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1363 / 800 : ℝ) - (681 / 1600 : ℝ)) ≤
      (204992591925103587 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1362_denomUpper
    linarith [hpThetaJensenCell1362_product_upper]
  have hi : (1 / (204992591925103587 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1363 / 800 : ℝ) - (681 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (204992591925103587 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (204992591925103587 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((681 / 1600 : ℝ) - Real.pi * Real.exp (1363 / 800 : ℝ)) := by
    rw [show (681 / 1600 : ℝ) - Real.pi * Real.exp (1363 / 800 : ℝ) =
      -(Real.pi * Real.exp (1363 / 800 : ℝ) - (681 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (681 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (681 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1362_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (204992591925103587 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1362_endpointUpper :
    hpThetaJensenKernelEndpointUpper (681 / 800 : ℝ) (1363 / 1600 : ℝ) ≤ (544057 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1363 / 800 : ℝ)) (34523048612975559 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1363 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1362_product_upper
  have hD : (200555783016371081 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (681 / 400 : ℝ) - (1363 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1362_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1362_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (681 / 400 : ℝ) - (1363 / 3200 : ℝ)) ≤
      (1 / (200555783016371081 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (200555783016371081 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1363 / 3200 : ℝ) - Real.pi * Real.exp (681 / 400 : ℝ)) ≤
      (2 / (200555783016371081 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1363 / 3200 : ℝ) - Real.pi * Real.exp (681 / 400 : ℝ) =
      -(Real.pi * Real.exp (681 / 400 : ℝ) - (1363 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (34523048612975559 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (34523048612975559 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1362_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (681 / 800 : ℝ) (1363 / 1600 : ℝ)) :
    (1058989 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (544057 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1362_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1362_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1363_leftExp :
    (6868141539 / 1250000000 : ℝ) ≤ Real.exp (1363 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1363 / 800 : ℝ) (42187401829 / 40000000000 : ℝ)
    (6868141539 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1363_rightExp :
    Real.exp (341 / 200 : ℝ) ≤ (55013856673 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (341 / 200 : ℝ) (210945249033 / 200000000000 : ℝ)
    (55013856673 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1363_denomUpper :
    Real.exp (168571772026900089 / 10000000000000000 : ℝ) ≤ (26175142373889343 / 1250000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (168571772026900089 / 10000000000000000 : ℝ)
    (1693482039357 / 1000000000000 : ℝ) (26175142373889343 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1363_denomLower :
    (40972677151241653 / 2000000000 : ℝ) ≤ Real.exp (2630510751723761 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2630510751723761 / 156250000000000 : ℝ) (211540376911 /
    125000000000 : ℝ) (40972677151241653 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1363_product_lower :
    (2697112314223761 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (1363 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1363_leftExp
    (by norm_num : (0 : ℝ) ≤ (6868141539 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1363_product_upper :
    Real.pi * Real.exp (341 / 200 : ℝ) ≤ (172831147026900089 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1363_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1363_endpointLower :
    (259853 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (1363 / 1600 : ℝ) (341 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2697112314223761 / 156250000000000 : ℝ) (Real.pi * Real.exp (1363 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1363_product_lower
  have hD : Real.exp (Real.pi * Real.exp (341 / 200 : ℝ) - (1363 / 3200 : ℝ)) ≤
      (26175142373889343 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1363_denomUpper
    linarith [hpThetaJensenCell1363_product_upper]
  have hi : (1 / (26175142373889343 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (341 / 200 : ℝ) - (1363 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (26175142373889343 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (26175142373889343 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1363 / 3200 : ℝ) - Real.pi * Real.exp (341 / 200 : ℝ)) := by
    rw [show (1363 / 3200 : ℝ) - Real.pi * Real.exp (341 / 200 : ℝ) =
      -(Real.pi * Real.exp (341 / 200 : ℝ) - (1363 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1363 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1363 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1363_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (26175142373889343 / 1250000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1363_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1363 / 1600 : ℝ) (341 / 400 : ℝ) ≤ (267007 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (341 / 200 : ℝ)) (172831147026900089 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (341 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1363_product_upper
  have hD : (40972677151241653 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1363 / 800 : ℝ) - (341 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1363_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1363_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1363 / 800 : ℝ) - (341 / 800 : ℝ)) ≤
      (1 / (40972677151241653 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (40972677151241653 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((341 / 800 : ℝ) - Real.pi * Real.exp (1363 / 800 : ℝ)) ≤
      (2 / (40972677151241653 / 2000000000 : ℝ) : ℝ) := by
    rw [show (341 / 800 : ℝ) - Real.pi * Real.exp (1363 / 800 : ℝ) =
      -(Real.pi * Real.exp (1363 / 800 : ℝ) - (341 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (172831147026900089 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (172831147026900089 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1363_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1363 / 1600 : ℝ) (341 / 400 : ℝ)) :
    (259853 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (267007 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1363_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1363_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1364_leftExp :
    (55013856671 / 10000000000 : ℝ) ≤ Real.exp (341 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (341 / 200 : ℝ) (263681561291 / 250000000000 : ℝ)
    (55013856671 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1364_rightExp :
    Real.exp (273 / 160 : ℝ) ≤ (3442666687 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (273 / 160 : ℝ) (527383723107 / 500000000000 : ℝ)
    (3442666687 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1364_denomUpper :
    Real.exp (10549051315212391 / 625000000000000 : ℝ) ≤ (213910272426948753 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (10549051315212391 / 625000000000000 : ℝ) (1694609898151
    / 1000000000000 : ℝ) (213910272426948753 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1364_denomLower :
    (26158644094648833 / 1250000000 : ℝ) ≤ Real.exp (21070683375845029 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (21070683375845029 / 1250000000000000 : ℝ) (1693448672689
    / 1000000000000 : ℝ) (26158644094648833 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1364_product_lower :
    (21603886500845029 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (341 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1364_leftExp
    (by norm_num : (0 : ℝ) ≤ (55013856671 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1364_product_upper :
    Real.pi * Real.exp (273 / 160 : ℝ) ≤ (10815457565212391 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1364_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1364_endpointLower :
    (102017 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (341 / 400 : ℝ) (273 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (21603886500845029 / 1250000000000000 : ℝ) (Real.pi * Real.exp (341 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1364_product_lower
  have hD : Real.exp (Real.pi * Real.exp (273 / 160 : ℝ) - (341 / 800 : ℝ)) ≤
      (213910272426948753 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1364_denomUpper
    linarith [hpThetaJensenCell1364_product_upper]
  have hi : (1 / (213910272426948753 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (273 / 160 : ℝ) - (341 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (213910272426948753 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (213910272426948753 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((341 / 800 : ℝ) - Real.pi * Real.exp (273 / 160 : ℝ)) := by
    rw [show (341 / 800 : ℝ) - Real.pi * Real.exp (273 / 160 : ℝ) =
      -(Real.pi * Real.exp (273 / 160 : ℝ) - (341 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (341 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (341 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1364_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (213910272426948753 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1364_endpointUpper :
    hpThetaJensenKernelEndpointUpper (341 / 400 : ℝ) (273 / 320 : ℝ) ≤ (209657 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (273 / 160 : ℝ)) (10815457565212391 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (273 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1364_product_upper
  have hD : (26158644094648833 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (341 / 200 : ℝ) - (273 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1364_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1364_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (341 / 200 : ℝ) - (273 / 640 : ℝ)) ≤
      (1 / (26158644094648833 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (26158644094648833 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((273 / 640 : ℝ) - Real.pi * Real.exp (341 / 200 : ℝ)) ≤
      (2 / (26158644094648833 / 1250000000 : ℝ) : ℝ) := by
    rw [show (273 / 640 : ℝ) - Real.pi * Real.exp (341 / 200 : ℝ) =
      -(Real.pi * Real.exp (341 / 200 : ℝ) - (273 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (10815457565212391 / 625000000000000 : ℝ) ^ 2 - 6 *
      (10815457565212391 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1364_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (341 / 400 : ℝ) (273 / 320 : ℝ)) :
    (102017 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (209657 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1364_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1364_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1365_leftExp :
    (5508266699 / 1000000000 : ℝ) ≤ Real.exp (273 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (273 / 160 : ℝ) (1054767446213 / 1000000000000 : ℝ)
    (5508266699 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1365_rightExp :
    Real.exp (683 / 400 : ℝ) ≤ (55151563377 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (683 / 400 : ℝ) (131851081109 / 125000000000 : ℝ)
    (55151563377 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1365_denomUpper :
    Real.exp (168998140444239561 / 10000000000000000 : ℝ) ≤ (218522411584802747 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (168998140444239561 / 10000000000000000 : ℝ)
    (423934985229 / 250000000000 : ℝ) (218522411584802747 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1365_denomLower :
    (213775442602596987 / 10000000000 : ℝ) ≤ Real.exp (2109731449430601 / 125000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (2109731449430601 / 125000000000000 : ℝ) (1694576508897 /
    1000000000000 : ℝ) (213775442602596987 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1365_product_lower :
    (2163090824430601 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (273 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1365_leftExp
    (by norm_num : (0 : ℝ) ≤ (5508266699 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1365_product_upper :
    Real.pi * Real.exp (683 / 400 : ℝ) ≤ (173263765444239561 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1365_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1365_endpointLower :
    (1001257 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (273 / 320 : ℝ) (683 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2163090824430601 / 125000000000000 : ℝ) (Real.pi * Real.exp (273 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1365_product_lower
  have hD : Real.exp (Real.pi * Real.exp (683 / 400 : ℝ) - (273 / 640 : ℝ)) ≤
      (218522411584802747 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1365_denomUpper
    linarith [hpThetaJensenCell1365_product_upper]
  have hi : (1 / (218522411584802747 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (683 / 400 : ℝ) - (273 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (218522411584802747 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (218522411584802747 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((273 / 640 : ℝ) - Real.pi * Real.exp (683 / 400 : ℝ)) := by
    rw [show (273 / 640 : ℝ) - Real.pi * Real.exp (683 / 400 : ℝ) =
      -(Real.pi * Real.exp (683 / 400 : ℝ) - (273 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (273 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (273 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1365_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (218522411584802747 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1365_endpointUpper :
    hpThetaJensenKernelEndpointUpper (273 / 320 : ℝ) (683 / 800 : ℝ) ≤ (514439 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (683 / 400 : ℝ)) (173263765444239561 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (683 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1365_product_upper
  have hD : (213775442602596987 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (273 / 160 : ℝ) - (683 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1365_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1365_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (273 / 160 : ℝ) - (683 / 1600 : ℝ)) ≤
      (1 / (213775442602596987 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (213775442602596987 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((683 / 1600 : ℝ) - Real.pi * Real.exp (273 / 160 : ℝ)) ≤
      (2 / (213775442602596987 / 10000000000 : ℝ) : ℝ) := by
    rw [show (683 / 1600 : ℝ) - Real.pi * Real.exp (273 / 160 : ℝ) =
      -(Real.pi * Real.exp (273 / 160 : ℝ) - (683 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (173263765444239561 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (173263765444239561 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1365_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (273 / 320 : ℝ) (683 / 800 : ℝ)) :
    (1001257 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (514439 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1365_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1365_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1366_leftExp :
    (441212507 / 80000000 : ℝ) ≤ Real.exp (683 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (683 / 400 : ℝ) (1054808648871 / 1000000000000 : ℝ)
    (441212507 / 80000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1366_rightExp :
    Real.exp (1367 / 800 : ℝ) ≤ (3451284121 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1367 / 800 : ℝ) (1054849853139 / 1000000000000 : ℝ)
    (3451284121 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1366_denomUpper :
    Real.exp (10575733160544753 / 625000000000000 : ℝ) ≤ (223240037057908101 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (10575733160544753 / 625000000000000 : ℝ) (848436086409 /
    500000000000 : ℝ) (223240037057908101 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1366_denomLower :
    (218384673175727627 / 10000000000 : ℝ) ≤ Real.exp (168991835286393 / 10000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (168991835286393 / 10000000000000 : ℝ) (1695706529031 /
    1000000000000 : ℝ) (218384673175727627 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1366_product_lower :
    (173263710286393 / 10000000000000 : ℝ) ≤ Real.pi * Real.exp (683 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1366_leftExp
    (by norm_num : (0 : ℝ) ≤ (441212507 / 80000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1366_product_upper :
    Real.pi * Real.exp (1367 / 800 : ℝ) ≤ (10842530035544753 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1366_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1366_endpointLower :
    (245667 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (683 / 800 : ℝ) (1367 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (173263710286393 / 10000000000000 : ℝ) (Real.pi * Real.exp (683 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1366_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1367 / 800 : ℝ) - (683 / 1600 : ℝ)) ≤
      (223240037057908101 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1366_denomUpper
    linarith [hpThetaJensenCell1366_product_upper]
  have hi : (1 / (223240037057908101 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1367 / 800 : ℝ) - (683 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (223240037057908101 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (223240037057908101 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((683 / 1600 : ℝ) - Real.pi * Real.exp (1367 / 800 : ℝ)) := by
    rw [show (683 / 1600 : ℝ) - Real.pi * Real.exp (1367 / 800 : ℝ) =
      -(Real.pi * Real.exp (1367 / 800 : ℝ) - (683 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (683 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (683 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1366_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (223240037057908101 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1366_endpointUpper :
    hpThetaJensenKernelEndpointUpper (683 / 800 : ℝ) (1367 / 1600 : ℝ) ≤ (1009803 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1367 / 800 : ℝ)) (10842530035544753 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1367 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1366_product_upper
  have hD : (218384673175727627 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (683 / 400 : ℝ) - (1367 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1366_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1366_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (683 / 400 : ℝ) - (1367 / 3200 : ℝ)) ≤
      (1 / (218384673175727627 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (218384673175727627 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1367 / 3200 : ℝ) - Real.pi * Real.exp (683 / 400 : ℝ)) ≤
      (2 / (218384673175727627 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1367 / 3200 : ℝ) - Real.pi * Real.exp (683 / 400 : ℝ) =
      -(Real.pi * Real.exp (683 / 400 : ℝ) - (1367 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (10842530035544753 / 625000000000000 : ℝ) ^ 2 - 6 *
      (10842530035544753 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1366_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (683 / 800 : ℝ) (1367 / 1600 : ℝ)) :
    (245667 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1009803 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1366_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1366_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1367_leftExp :
    (55220545933 / 10000000000 : ℝ) ≤ Real.exp (1367 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1367 / 800 : ℝ) (527424926569 / 500000000000 : ℝ)
    (55220545933 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1367_rightExp :
    Real.exp (171 / 100 : ℝ) ≤ (27644807389 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (171 / 100 : ℝ) (1054891059017 / 1000000000000 : ℝ)
    (27644807389 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1367_denomUpper :
    Real.exp (84712795879630677 / 5000000000000000 : ℝ) ≤ (57016423039972021 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (84712795879630677 / 5000000000000000 : ℝ) (33960131981 /
    20000000000 : ℝ) (57016423039972021 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1367_denomLower :
    (223099323436848231 / 10000000000 : ℝ) ≤ Real.exp (21150678167343167 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (21150678167343167 / 1250000000000000 : ℝ) (1696838738241
    / 1000000000000 : ℝ) (223099323436848231 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1367_product_lower :
    (21685053167343167 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1367 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1367_leftExp
    (by norm_num : (0 : ℝ) ≤ (55220545933 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1367_product_upper :
    Real.pi * Real.exp (171 / 100 : ℝ) ≤ (86848733379630677 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1367_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1367_endpointLower :
    (964397 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1367 / 1600 : ℝ) (171 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (21685053167343167 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1367 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1367_product_lower
  have hD : Real.exp (Real.pi * Real.exp (171 / 100 : ℝ) - (1367 / 3200 : ℝ)) ≤
      (57016423039972021 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1367_denomUpper
    linarith [hpThetaJensenCell1367_product_upper]
  have hi : (1 / (57016423039972021 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (171 / 100 : ℝ) - (1367 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (57016423039972021 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (57016423039972021 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1367 / 3200 : ℝ) - Real.pi * Real.exp (171 / 100 : ℝ)) := by
    rw [show (1367 / 3200 : ℝ) - Real.pi * Real.exp (171 / 100 : ℝ) =
      -(Real.pi * Real.exp (171 / 100 : ℝ) - (1367 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1367 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1367 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1367_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (57016423039972021 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1367_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1367 / 1600 : ℝ) (171 / 200 : ℝ) ≤ (198211 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (171 / 100 : ℝ)) (86848733379630677 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (171 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1367_product_upper
  have hD : (223099323436848231 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1367 / 800 : ℝ) - (171 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1367_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1367_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1367 / 800 : ℝ) - (171 / 400 : ℝ)) ≤
      (1 / (223099323436848231 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (223099323436848231 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((171 / 400 : ℝ) - Real.pi * Real.exp (1367 / 800 : ℝ)) ≤
      (2 / (223099323436848231 / 10000000000 : ℝ) : ℝ) := by
    rw [show (171 / 400 : ℝ) - Real.pi * Real.exp (1367 / 800 : ℝ) =
      -(Real.pi * Real.exp (1367 / 800 : ℝ) - (171 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (86848733379630677 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (86848733379630677 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1367_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1367 / 1600 : ℝ) (171 / 200 : ℝ)) :
    (964397 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (198211 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1367_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1367_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1368_leftExp :
    (6911201847 / 1250000000 : ℝ) ≤ Real.exp (171 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (171 / 100 : ℝ) (131861382377 / 125000000000 : ℝ)
    (6911201847 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1368_rightExp :
    Real.exp (1369 / 800 : ℝ) ≤ (6919846251 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1369 / 800 : ℝ) (1054932266503 / 1000000000000 : ℝ)
    (6919846251 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1368_denomUpper :
    Real.exp (21204965543217843 / 1250000000000000 : ℝ) ≤ (1820328001925267 / 78125000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21204965543217843 / 1250000000000000 : ℝ) (339828644951
    / 200000000000 : ℝ) (1820328001925267 / 78125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1368_denomLower :
    (113960967654595641 / 5000000000 : ℝ) ≤ Real.exp (2647176350990053 / 156250000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (2647176350990053 / 156250000000000 : ℝ) (1697973141771 /
    1000000000000 : ℝ) (113960967654595641 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1368_product_lower :
    (2714022054115053 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (171 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1368_leftExp
    (by norm_num : (0 : ℝ) ≤ (6911201847 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1368_product_upper :
    Real.pi * Real.exp (1369 / 800 : ℝ) ≤ (21739340543217843 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1368_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1368_endpointLower :
    (946441 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (171 / 200 : ℝ) (1369 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2714022054115053 / 156250000000000 : ℝ) (Real.pi * Real.exp (171 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1368_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1369 / 800 : ℝ) - (171 / 400 : ℝ)) ≤
      (1820328001925267 / 78125000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1368_denomUpper
    linarith [hpThetaJensenCell1368_product_upper]
  have hi : (1 / (1820328001925267 / 78125000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1369 / 800 : ℝ) - (171 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1820328001925267 / 78125000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1820328001925267 / 78125000 : ℝ) : ℝ) ≤
      2 * Real.exp ((171 / 400 : ℝ) - Real.pi * Real.exp (1369 / 800 : ℝ)) := by
    rw [show (171 / 400 : ℝ) - Real.pi * Real.exp (1369 / 800 : ℝ) =
      -(Real.pi * Real.exp (1369 / 800 : ℝ) - (171 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (171 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (171 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1368_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1820328001925267 / 78125000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1368_endpointUpper :
    hpThetaJensenKernelEndpointUpper (171 / 200 : ℝ) (1369 / 1600 : ℝ) ≤ (243157 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1369 / 800 : ℝ)) (21739340543217843 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1369 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1368_product_upper
  have hD : (113960967654595641 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (171 / 100 : ℝ) - (1369 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1368_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1368_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (171 / 100 : ℝ) - (1369 / 3200 : ℝ)) ≤
      (1 / (113960967654595641 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (113960967654595641 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1369 / 3200 : ℝ) - Real.pi * Real.exp (171 / 100 : ℝ)) ≤
      (2 / (113960967654595641 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1369 / 3200 : ℝ) - Real.pi * Real.exp (171 / 100 : ℝ) =
      -(Real.pi * Real.exp (171 / 100 : ℝ) - (1369 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (21739340543217843 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (21739340543217843 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1368_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (171 / 200 : ℝ) (1369 / 1600 : ℝ)) :
    (946441 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (243157 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1368_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1368_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1369_leftExp :
    (27679385003 / 5000000000 : ℝ) ≤ Real.exp (1369 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1369 / 800 : ℝ) (527466133251 / 500000000000 : ℝ)
    (27679385003 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1369_rightExp :
    Real.exp (137 / 80 : ℝ) ≤ (55428011739 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (137 / 80 : ℝ) (2637433689 / 2500000000 : ℝ)
    (55428011739 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1369_denomUpper :
    Real.exp (169854128683160227 / 10000000000000000 : ℝ) ≤ (238051587254394769 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (169854128683160227 / 10000000000000000 : ℝ) (85014102761
    / 50000000000 : ℝ) (238051587254394769 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1369_denomLower :
    (232855114288499081 / 10000000000 : ℝ) ≤ Real.exp (10602088686293097 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (10602088686293097 / 625000000000000 : ℝ) (1699109744713
    / 1000000000000 : ℝ) (232855114288499081 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1369_product_lower :
    (10869666811293097 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1369 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1369_leftExp
    (by norm_num : (0 : ℝ) ≤ (27679385003 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1369_product_upper :
    Real.pi * Real.exp (137 / 80 : ℝ) ≤ (174132253683160227 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1369_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1369_endpointLower :
    (928793 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1369 / 1600 : ℝ) (137 / 160 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10869666811293097 / 625000000000000 : ℝ) (Real.pi * Real.exp (1369 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1369_product_lower
  have hD : Real.exp (Real.pi * Real.exp (137 / 80 : ℝ) - (1369 / 3200 : ℝ)) ≤
      (238051587254394769 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1369_denomUpper
    linarith [hpThetaJensenCell1369_product_upper]
  have hi : (1 / (238051587254394769 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (137 / 80 : ℝ) - (1369 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (238051587254394769 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (238051587254394769 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1369 / 3200 : ℝ) - Real.pi * Real.exp (137 / 80 : ℝ)) := by
    rw [show (1369 / 3200 : ℝ) - Real.pi * Real.exp (137 / 80 : ℝ) =
      -(Real.pi * Real.exp (137 / 80 : ℝ) - (1369 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1369 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1369 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1369_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (238051587254394769 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1369_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1369 / 1600 : ℝ) (137 / 160 : ℝ) ≤ (477259 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (137 / 80 : ℝ)) (174132253683160227 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (137 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1369_product_upper
  have hD : (232855114288499081 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1369 / 800 : ℝ) - (137 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell1369_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1369_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1369 / 800 : ℝ) - (137 / 320 : ℝ)) ≤
      (1 / (232855114288499081 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (232855114288499081 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((137 / 320 : ℝ) - Real.pi * Real.exp (1369 / 800 : ℝ)) ≤
      (2 / (232855114288499081 / 10000000000 : ℝ) : ℝ) := by
    rw [show (137 / 320 : ℝ) - Real.pi * Real.exp (1369 / 800 : ℝ) =
      -(Real.pi * Real.exp (1369 / 800 : ℝ) - (137 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (174132253683160227 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (174132253683160227 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1369_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1369 / 1600 : ℝ) (137 / 160 : ℝ)) :
    (928793 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (477259 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1369_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1369_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1370_leftExp :
    (6928501467 / 1250000000 : ℝ) ≤ Real.exp (137 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (137 / 80 : ℝ) (1054973475599 / 1000000000000 : ℝ)
    (6928501467 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1370_rightExp :
    Real.exp (1371 / 800 : ℝ) ≤ (27748670037 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1371 / 800 : ℝ) (527507343153 / 500000000000 : ℝ)
    (27748670037 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1370_denomUpper :
    Real.exp (85034402547548941 / 5000000000000000 : ℝ) ≤ (121608621072312289 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (85034402547548941 / 5000000000000000 : ℝ) (850711547789
    / 500000000000 : ℝ) (121608621072312289 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1370_denomLower :
    (237901532619658843 / 10000000000 : ℝ) ≤ Real.exp (2653872238214433 / 156250000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (2653872238214433 / 156250000000000 : ℝ) (850124276177 /
    500000000000 : ℝ) (237901532619658843 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1370_product_lower :
    (2720815597589433 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (137 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1370_leftExp
    (by norm_num : (0 : ℝ) ≤ (6928501467 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1370_product_upper :
    Real.pi * Real.exp (1371 / 800 : ℝ) ≤ (87175027547548941 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1370_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1370_endpointLower :
    (911449 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (137 / 160 : ℝ) (1371 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2720815597589433 / 156250000000000 : ℝ) (Real.pi * Real.exp (137 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell1370_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1371 / 800 : ℝ) - (137 / 320 : ℝ)) ≤
      (121608621072312289 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1370_denomUpper
    linarith [hpThetaJensenCell1370_product_upper]
  have hi : (1 / (121608621072312289 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1371 / 800 : ℝ) - (137 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (121608621072312289 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (121608621072312289 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((137 / 320 : ℝ) - Real.pi * Real.exp (1371 / 800 : ℝ)) := by
    rw [show (137 / 320 : ℝ) - Real.pi * Real.exp (1371 / 800 : ℝ) =
      -(Real.pi * Real.exp (1371 / 800 : ℝ) - (137 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (137 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (137 / 80 : ℝ)) := by
    have h := hpThetaJensenCell1370_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (121608621072312289 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1370_endpointUpper :
    hpThetaJensenKernelEndpointUpper (137 / 160 : ℝ) (1371 / 1600 : ℝ) ≤ (936719 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1371 / 800 : ℝ)) (87175027547548941 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1371 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1370_product_upper
  have hD : (237901532619658843 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (137 / 80 : ℝ) - (1371 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1370_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1370_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (137 / 80 : ℝ) - (1371 / 3200 : ℝ)) ≤
      (1 / (237901532619658843 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (237901532619658843 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1371 / 3200 : ℝ) - Real.pi * Real.exp (137 / 80 : ℝ)) ≤
      (2 / (237901532619658843 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1371 / 3200 : ℝ) - Real.pi * Real.exp (137 / 80 : ℝ) =
      -(Real.pi * Real.exp (137 / 80 : ℝ) - (1371 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (87175027547548941 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (87175027547548941 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1370_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (137 / 160 : ℝ) (1371 / 1600 : ℝ)) :
    (911449 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (936719 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1370_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1370_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1371_leftExp :
    (6937167509 / 1250000000 : ℝ) ≤ Real.exp (1371 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1371 / 800 : ℝ) (211002937261 / 200000000000 : ℝ)
    (6937167509 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1371_rightExp :
    Real.exp (343 / 200 : ℝ) ≤ (444534041 / 80000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (343 / 200 : ℝ) (527527949311 / 500000000000 : ℝ)
    (444534041 / 80000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1371_denomUpper :
    Real.exp (1362270031467313 / 80000000000000 : ℝ) ≤ (124250880046304053 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1362270031467313 / 80000000000000 : ℝ) (425641587781 /
    250000000000 : ℝ) (124250880046304053 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1371_denomLower :
    (121531964876533407 / 5000000000 : ℝ) ≤ Real.exp (2657226556116791 / 156250000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (2657226556116791 / 156250000000000 : ℝ) (425347392469 /
    250000000000 : ℝ) (121531964876533407 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1371_product_lower :
    (2724218743616791 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (1371 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1371_leftExp
    (by norm_num : (0 : ℝ) ≤ (6937167509 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1371_product_upper :
    Real.pi * Real.exp (343 / 200 : ℝ) ≤ (1396545031467313 / 80000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1371_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1371_endpointLower :
    (178881 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1371 / 1600 : ℝ) (343 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2724218743616791 / 156250000000000 : ℝ) (Real.pi * Real.exp (1371 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1371_product_lower
  have hD : Real.exp (Real.pi * Real.exp (343 / 200 : ℝ) - (1371 / 3200 : ℝ)) ≤
      (124250880046304053 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1371_denomUpper
    linarith [hpThetaJensenCell1371_product_upper]
  have hi : (1 / (124250880046304053 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (343 / 200 : ℝ) - (1371 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (124250880046304053 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (124250880046304053 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1371 / 3200 : ℝ) - Real.pi * Real.exp (343 / 200 : ℝ)) := by
    rw [show (1371 / 3200 : ℝ) - Real.pi * Real.exp (343 / 200 : ℝ) =
      -(Real.pi * Real.exp (343 / 200 : ℝ) - (1371 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1371 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1371 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1371_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (124250880046304053 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1371_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1371 / 1600 : ℝ) (343 / 400 : ℝ) ≤ (229807 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (343 / 200 : ℝ)) (1396545031467313 / 80000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (343 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1371_product_upper
  have hD : (121531964876533407 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1371 / 800 : ℝ) - (343 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1371_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1371_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1371 / 800 : ℝ) - (343 / 800 : ℝ)) ≤
      (1 / (121531964876533407 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (121531964876533407 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((343 / 800 : ℝ) - Real.pi * Real.exp (1371 / 800 : ℝ)) ≤
      (2 / (121531964876533407 / 5000000000 : ℝ) : ℝ) := by
    rw [show (343 / 800 : ℝ) - Real.pi * Real.exp (1371 / 800 : ℝ) =
      -(Real.pi * Real.exp (1371 / 800 : ℝ) - (343 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1396545031467313 / 80000000000000 : ℝ) ^ 2 - 6 *
      (1396545031467313 / 80000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1371_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1371 / 1600 : ℝ) (343 / 400 : ℝ)) :
    (178881 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (229807 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1371_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1371_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1372_leftExp :
    (27783377561 / 5000000000 : ℝ) ≤ Real.exp (343 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (343 / 200 : ℝ) (1055055898621 / 1000000000000 : ℝ)
    (27783377561 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1372_rightExp :
    Real.exp (1373 / 800 : ℝ) ≤ (27818128499 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1373 / 800 : ℝ) (263774278137 / 250000000000 : ℝ)
    (27818128499 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1372_denomUpper :
    Real.exp (85249487765558907 / 5000000000000000 : ℝ) ≤ (253908023224775187 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (85249487765558907 / 5000000000000000 : ℝ) (425927956767
    / 250000000000 : ℝ) (253908023224775187 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1372_denomLower :
    (31043139349497427 / 1250000000 : ℝ) ≤ Real.exp (10642340522327139 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (10642340522327139 / 625000000000000 : ℝ) (1702532802509
    / 1000000000000 : ℝ) (31043139349497427 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1372_product_lower :
    (10910504584827139 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (343 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1372_leftExp
    (by norm_num : (0 : ℝ) ≤ (27783377561 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1372_product_upper :
    Real.pi * Real.exp (1373 / 800 : ℝ) ≤ (87393237765558907 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1372_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1372_endpointLower :
    (109707 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (343 / 400 : ℝ) (1373 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10910504584827139 / 625000000000000 : ℝ) (Real.pi * Real.exp (343 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1372_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1373 / 800 : ℝ) - (343 / 800 : ℝ)) ≤
      (253908023224775187 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1372_denomUpper
    linarith [hpThetaJensenCell1372_product_upper]
  have hi : (1 / (253908023224775187 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1373 / 800 : ℝ) - (343 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (253908023224775187 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (253908023224775187 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((343 / 800 : ℝ) - Real.pi * Real.exp (1373 / 800 : ℝ)) := by
    rw [show (343 / 800 : ℝ) - Real.pi * Real.exp (1373 / 800 : ℝ) =
      -(Real.pi * Real.exp (1373 / 800 : ℝ) - (343 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (343 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (343 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1372_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (253908023224775187 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1372_endpointUpper :
    hpThetaJensenKernelEndpointUpper (343 / 400 : ℝ) (1373 / 1600 : ℝ) ≤ (451019 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1373 / 800 : ℝ)) (87393237765558907 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1373 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1372_product_upper
  have hD : (31043139349497427 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (343 / 200 : ℝ) - (1373 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1372_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1372_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (343 / 200 : ℝ) - (1373 / 3200 : ℝ)) ≤
      (1 / (31043139349497427 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (31043139349497427 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1373 / 3200 : ℝ) - Real.pi * Real.exp (343 / 200 : ℝ)) ≤
      (2 / (31043139349497427 / 1250000000 : ℝ) : ℝ) := by
    rw [show (1373 / 3200 : ℝ) - Real.pi * Real.exp (343 / 200 : ℝ) =
      -(Real.pi * Real.exp (343 / 200 : ℝ) - (1373 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (87393237765558907 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (87393237765558907 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1372_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (343 / 400 : ℝ) (1373 / 1600 : ℝ)) :
    (109707 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (451019 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1372_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1372_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1373_leftExp :
    (11127251399 / 2000000000 : ℝ) ≤ Real.exp (1373 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1373 / 800 : ℝ) (1055097112547 / 1000000000000 : ℝ)
    (11127251399 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1373_rightExp :
    Real.exp (687 / 400 : ℝ) ≤ (55705845803 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (687 / 400 : ℝ) (263784582021 / 250000000000 : ℝ)
    (55705845803 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1373_denomUpper :
    Real.exp (170714470233784179 / 10000000000000000 : ℝ) ≤ (259438987257912213 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (170714470233784179 / 10000000000000000 : ℝ)
    (852429764349 / 500000000000 : ℝ) (259438987257912213 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1373_denomLower :
    (253747968280007757 / 10000000000 : ℝ) ≤ Real.exp (4262316747135901 / 250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (4262316747135901 / 250000000000000 : ℝ) (212959781939 /
    125000000000 : ℝ) (253747968280007757 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1373_product_lower :
    (4369660497135901 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1373 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1373_leftExp
    (by norm_num : (0 : ℝ) ≤ (11127251399 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1373_product_upper :
    Real.pi * Real.exp (687 / 400 : ℝ) ≤ (175005095233784179 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1373_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1373_endpointLower :
    (215299 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (1373 / 1600 : ℝ) (687 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4369660497135901 / 250000000000000 : ℝ) (Real.pi * Real.exp (1373 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1373_product_lower
  have hD : Real.exp (Real.pi * Real.exp (687 / 400 : ℝ) - (1373 / 3200 : ℝ)) ≤
      (259438987257912213 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1373_denomUpper
    linarith [hpThetaJensenCell1373_product_upper]
  have hi : (1 / (259438987257912213 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (687 / 400 : ℝ) - (1373 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (259438987257912213 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (259438987257912213 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1373 / 3200 : ℝ) - Real.pi * Real.exp (687 / 400 : ℝ)) := by
    rw [show (1373 / 3200 : ℝ) - Real.pi * Real.exp (687 / 400 : ℝ) =
      -(Real.pi * Real.exp (687 / 400 : ℝ) - (1373 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1373 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1373 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1373_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (259438987257912213 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1373_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1373 / 1600 : ℝ) (687 / 800 : ℝ) ≤ (177029 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (687 / 400 : ℝ)) (175005095233784179 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (687 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1373_product_upper
  have hD : (253747968280007757 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1373 / 800 : ℝ) - (687 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1373_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1373_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1373 / 800 : ℝ) - (687 / 1600 : ℝ)) ≤
      (1 / (253747968280007757 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (253747968280007757 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((687 / 1600 : ℝ) - Real.pi * Real.exp (1373 / 800 : ℝ)) ≤
      (2 / (253747968280007757 / 10000000000 : ℝ) : ℝ) := by
    rw [show (687 / 1600 : ℝ) - Real.pi * Real.exp (1373 / 800 : ℝ) =
      -(Real.pi * Real.exp (1373 / 800 : ℝ) - (687 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (175005095233784179 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (175005095233784179 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1373_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1373 / 1600 : ℝ) (687 / 800 : ℝ)) :
    (215299 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (177029 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1373_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1373_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1374_leftExp :
    (55705845801 / 10000000000 : ℝ) ≤ Real.exp (687 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (687 / 400 : ℝ) (1055138328083 / 1000000000000 : ℝ)
    (55705845801 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1374_rightExp :
    Real.exp (55 / 32 : ℝ) ≤ (55775521649 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (55 / 32 : ℝ) (105517954523 / 100000000000 : ℝ)
    (55775521649 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1374_denomUpper :
    Real.exp (170930238383846857 / 10000000000000000 : ℝ) ≤ (258884456122967 / 9765625 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (170930238383846857 / 10000000000000000 : ℝ)
    (853004730649 / 500000000000 : ℝ) (258884456122967 / 9765625 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1374_denomLower :
    (259275444056642417 / 10000000000 : ℝ) ≤ Real.exp (21338520565206899 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (21338520565206899 / 1250000000000000 : ℝ) (426206483543
    / 250000000000 : ℝ) (259275444056642417 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1374_product_lower :
    (21875629940206899 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (687 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1374_leftExp
    (by norm_num : (0 : ℝ) ≤ (55705845801 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1374_product_upper :
    Real.pi * Real.exp (55 / 32 : ℝ) ≤ (175223988383846857 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1374_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1374_endpointLower :
    (422511 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (687 / 800 : ℝ) (55 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (21875629940206899 / 1250000000000000 : ℝ) (Real.pi * Real.exp (687 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1374_product_lower
  have hD : Real.exp (Real.pi * Real.exp (55 / 32 : ℝ) - (687 / 1600 : ℝ)) ≤
      (258884456122967 / 9765625 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1374_denomUpper
    linarith [hpThetaJensenCell1374_product_upper]
  have hi : (1 / (258884456122967 / 9765625 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (55 / 32 : ℝ) - (687 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (258884456122967 / 9765625 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (258884456122967 / 9765625 : ℝ) : ℝ) ≤
      2 * Real.exp ((687 / 1600 : ℝ) - Real.pi * Real.exp (55 / 32 : ℝ)) := by
    rw [show (687 / 1600 : ℝ) - Real.pi * Real.exp (55 / 32 : ℝ) =
      -(Real.pi * Real.exp (55 / 32 : ℝ) - (687 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (687 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (687 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1374_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (258884456122967 / 9765625 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1374_endpointUpper :
    hpThetaJensenKernelEndpointUpper (687 / 800 : ℝ) (55 / 64 : ℝ) ≤ (173709 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (55 / 32 : ℝ)) (175223988383846857 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (55 / 64 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1374_product_upper
  have hD : (259275444056642417 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (687 / 400 : ℝ) - (55 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell1374_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1374_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (687 / 400 : ℝ) - (55 / 128 : ℝ)) ≤
      (1 / (259275444056642417 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (259275444056642417 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((55 / 128 : ℝ) - Real.pi * Real.exp (687 / 400 : ℝ)) ≤
      (2 / (259275444056642417 / 10000000000 : ℝ) : ℝ) := by
    rw [show (55 / 128 : ℝ) - Real.pi * Real.exp (687 / 400 : ℝ) =
      -(Real.pi * Real.exp (687 / 400 : ℝ) - (55 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (175223988383846857 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (175223988383846857 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1374_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (687 / 800 : ℝ) (55 / 64 : ℝ)) :
    (422511 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (173709 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1374_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1374_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1375_leftExp :
    (27887760823 / 5000000000 : ℝ) ≤ Real.exp (55 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (55 / 32 : ℝ) (1055179545229 / 1000000000000 : ℝ)
    (27887760823 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1375_rightExp :
    Real.exp (43 / 25 : ℝ) ≤ (13961321161 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (43 / 25 : ℝ) (527610381993 / 500000000000 : ℝ)
    (13961321161 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1375_denomUpper :
    Real.exp (42786570080149473 / 2500000000000000 : ℝ) ≤ (529076599025997 / 19531250 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (42786570080149473 / 2500000000000000 : ℝ) (34143232603 /
    20000000000 : ℝ) (529076599025997 / 19531250 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1375_denomLower :
    (264930570857308059 / 10000000000 : ℝ) ≤ Real.exp (10682745787431277 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (10682745787431277 / 625000000000000 : ℝ) (68239033749 /
    40000000000 : ℝ) (264930570857308059 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1375_product_lower :
    (10951495787431277 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (55 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1375_leftExp
    (by norm_num : (0 : ℝ) ≤ (27887760823 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1375_product_upper :
    Real.pi * Real.exp (43 / 25 : ℝ) ≤ (43860788830149473 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1375_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1375_endpointLower :
    (829129 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (55 / 64 : ℝ) (43 / 50 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10951495787431277 / 625000000000000 : ℝ) (Real.pi * Real.exp (55 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell1375_product_lower
  have hD : Real.exp (Real.pi * Real.exp (43 / 25 : ℝ) - (55 / 128 : ℝ)) ≤
      (529076599025997 / 19531250 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1375_denomUpper
    linarith [hpThetaJensenCell1375_product_upper]
  have hi : (1 / (529076599025997 / 19531250 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (43 / 25 : ℝ) - (55 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (529076599025997 / 19531250 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (529076599025997 / 19531250 : ℝ) : ℝ) ≤
      2 * Real.exp ((55 / 128 : ℝ) - Real.pi * Real.exp (43 / 25 : ℝ)) := by
    rw [show (55 / 128 : ℝ) - Real.pi * Real.exp (43 / 25 : ℝ) =
      -(Real.pi * Real.exp (43 / 25 : ℝ) - (55 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (55 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (55 / 32 : ℝ)) := by
    have h := hpThetaJensenCell1375_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (529076599025997 / 19531250 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1375_endpointUpper :
    hpThetaJensenKernelEndpointUpper (55 / 64 : ℝ) (43 / 50 : ℝ) ≤ (106529 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (43 / 25 : ℝ)) (43860788830149473 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (43 / 50 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1375_product_upper
  have hD : (264930570857308059 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (55 / 32 : ℝ) - (43 / 100 : ℝ)) := by
    apply le_trans hpThetaJensenCell1375_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1375_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (55 / 32 : ℝ) - (43 / 100 : ℝ)) ≤
      (1 / (264930570857308059 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (264930570857308059 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((43 / 100 : ℝ) - Real.pi * Real.exp (55 / 32 : ℝ)) ≤
      (2 / (264930570857308059 / 10000000000 : ℝ) : ℝ) := by
    rw [show (43 / 100 : ℝ) - Real.pi * Real.exp (55 / 32 : ℝ) =
      -(Real.pi * Real.exp (55 / 32 : ℝ) - (43 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (43860788830149473 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (43860788830149473 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1375_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (55 / 64 : ℝ) (43 / 50 : ℝ)) :
    (829129 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (106529 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1375_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1375_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1376_leftExp :
    (55845284641 / 10000000000 : ℝ) ≤ Real.exp (43 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (43 / 25 : ℝ) (211044152797 / 200000000000 : ℝ)
    (55845284641 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1376_rightExp :
    Real.exp (1377 / 800 : ℝ) ≤ (55915134897 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1377 / 800 : ℝ) (32976937011 / 31250000000 : ℝ)
    (55915134897 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1376_denomUpper :
    Real.exp (171362596386470921 / 10000000000000000 : ℝ) ≤ (69202695388186563 / 2500000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (171362596386470921 / 10000000000000000 : ℝ)
    (1708316040563 / 1000000000000 : ℝ) (69202695388186563 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1376_denomLower :
    (54143290997896323 / 2000000000 : ℝ) ≤ Real.exp (21392496808236059 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (21392496808236059 / 1250000000000000 : ℝ) (3414255979 /
    2000000000 : ℝ) (54143290997896323 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1376_product_lower :
    (21930387433236059 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (43 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1376_leftExp
    (by norm_num : (0 : ℝ) ≤ (55845284641 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1376_product_upper :
    Real.pi * Real.exp (1377 / 800 : ℝ) ≤ (175662596386470921 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1376_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1376_endpointLower :
    (101689 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (43 / 50 : ℝ) (1377 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (21930387433236059 / 1250000000000000 : ℝ) (Real.pi * Real.exp (43 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell1376_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1377 / 800 : ℝ) - (43 / 100 : ℝ)) ≤
      (69202695388186563 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1376_denomUpper
    linarith [hpThetaJensenCell1376_product_upper]
  have hi : (1 / (69202695388186563 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1377 / 800 : ℝ) - (43 / 100 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (69202695388186563 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (69202695388186563 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((43 / 100 : ℝ) - Real.pi * Real.exp (1377 / 800 : ℝ)) := by
    rw [show (43 / 100 : ℝ) - Real.pi * Real.exp (1377 / 800 : ℝ) =
      -(Real.pi * Real.exp (1377 / 800 : ℝ) - (43 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (43 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (43 / 25 : ℝ)) := by
    have h := hpThetaJensenCell1376_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (69202695388186563 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1376_endpointUpper :
    hpThetaJensenKernelEndpointUpper (43 / 50 : ℝ) (1377 / 1600 : ℝ) ≤ (836203 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1377 / 800 : ℝ)) (175662596386470921 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1377 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1376_product_upper
  have hD : (54143290997896323 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (43 / 25 : ℝ) - (1377 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1376_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1376_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (43 / 25 : ℝ) - (1377 / 3200 : ℝ)) ≤
      (1 / (54143290997896323 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (54143290997896323 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1377 / 3200 : ℝ) - Real.pi * Real.exp (43 / 25 : ℝ)) ≤
      (2 / (54143290997896323 / 2000000000 : ℝ) : ℝ) := by
    rw [show (1377 / 3200 : ℝ) - Real.pi * Real.exp (43 / 25 : ℝ) =
      -(Real.pi * Real.exp (43 / 25 : ℝ) - (1377 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (175662596386470921 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (175662596386470921 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1376_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (43 / 50 : ℝ) (1377 / 1600 : ℝ)) :
    (101689 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (836203 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1376_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1376_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1377_leftExp :
    (27957567447 / 5000000000 : ℝ) ≤ Real.exp (1377 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1377 / 800 : ℝ) (1055261984351 / 1000000000000 : ℝ)
    (27957567447 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1377_rightExp :
    Real.exp (689 / 400 : ℝ) ≤ (27992536259 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (689 / 400 : ℝ) (1055303206329 / 1000000000000 : ℝ)
    (27992536259 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1377_denomUpper :
    Real.exp (85789593463520587 / 5000000000000000 : ℝ) ≤ (282871640536239207 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (85789593463520587 / 5000000000000000 : ℝ) (1709472697879
    / 1000000000000 : ℝ) (282871640536239207 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1377_denomLower :
    (69159070444884433 / 2500000000 : ℝ) ≤ Real.exp (10709768153869453 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (10709768153869453 / 625000000000000 : ℝ) (1708282376793
    / 1000000000000 : ℝ) (69159070444884433 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1377_product_lower :
    (10978908778869453 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1377 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1377_leftExp
    (by norm_num : (0 : ℝ) ≤ (27957567447 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1377_product_upper :
    Real.pi * Real.exp (689 / 400 : ℝ) ≤ (87941155963520587 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1377_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1377_endpointLower :
    (99771 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (1377 / 1600 : ℝ) (689 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10978908778869453 / 625000000000000 : ℝ) (Real.pi * Real.exp (1377 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1377_product_lower
  have hD : Real.exp (Real.pi * Real.exp (689 / 400 : ℝ) - (1377 / 3200 : ℝ)) ≤
      (282871640536239207 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1377_denomUpper
    linarith [hpThetaJensenCell1377_product_upper]
  have hi : (1 / (282871640536239207 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (689 / 400 : ℝ) - (1377 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (282871640536239207 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (282871640536239207 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1377 / 3200 : ℝ) - Real.pi * Real.exp (689 / 400 : ℝ)) := by
    rw [show (1377 / 3200 : ℝ) - Real.pi * Real.exp (689 / 400 : ℝ) =
      -(Real.pi * Real.exp (689 / 400 : ℝ) - (1377 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1377 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1377 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1377_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (282871640536239207 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1377_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1377 / 1600 : ℝ) (689 / 800 : ℝ) ≤ (820453 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (689 / 400 : ℝ)) (87941155963520587 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (689 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1377_product_upper
  have hD : (69159070444884433 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1377 / 800 : ℝ) - (689 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1377_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1377_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1377 / 800 : ℝ) - (689 / 1600 : ℝ)) ≤
      (1 / (69159070444884433 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (69159070444884433 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((689 / 1600 : ℝ) - Real.pi * Real.exp (1377 / 800 : ℝ)) ≤
      (2 / (69159070444884433 / 2500000000 : ℝ) : ℝ) := by
    rw [show (689 / 1600 : ℝ) - Real.pi * Real.exp (1377 / 800 : ℝ) =
      -(Real.pi * Real.exp (1377 / 800 : ℝ) - (689 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (87941155963520587 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (87941155963520587 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1377_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1377 / 1600 : ℝ) (689 / 800 : ℝ)) :
    (99771 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (820453 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1377_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1377_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1378_leftExp :
    (13996268129 / 2500000000 : ℝ) ≤ Real.exp (689 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (689 / 400 : ℝ) (131912900791 / 125000000000 : ℝ)
    (13996268129 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1378_rightExp :
    Real.exp (1379 / 800 : ℝ) ≤ (28027548807 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1379 / 800 : ℝ) (211068885983 / 200000000000 : ℝ)
    (28027548807 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1378_denomUpper :
    Real.exp (85898026139229551 / 5000000000000000 : ℝ) ≤ (72268286966916463 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (85898026139229551 / 5000000000000000 : ℝ) (1710631607401
    / 1000000000000 : ℝ) (72268286966916463 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1378_denomLower :
    (282693318145867371 / 10000000000 : ℝ) ≤ Real.exp (5361652529240171 / 312500000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (5361652529240171 / 312500000000000 : ℝ) (1709439010959 /
    1000000000000 : ℝ) (282693318145867371 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1378_product_lower :
    (5496320497990171 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (689 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1378_leftExp
    (by norm_num : (0 : ℝ) ≤ (13996268129 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1378_product_upper :
    Real.pi * Real.exp (1379 / 800 : ℝ) ≤ (88051151139229551 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1378_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1378_endpointLower :
    (783091 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (689 / 800 : ℝ) (1379 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5496320497990171 / 312500000000000 : ℝ) (Real.pi * Real.exp (689 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1378_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1379 / 800 : ℝ) - (689 / 1600 : ℝ)) ≤
      (72268286966916463 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1378_denomUpper
    linarith [hpThetaJensenCell1378_product_upper]
  have hi : (1 / (72268286966916463 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1379 / 800 : ℝ) - (689 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (72268286966916463 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (72268286966916463 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((689 / 1600 : ℝ) - Real.pi * Real.exp (1379 / 800 : ℝ)) := by
    rw [show (689 / 1600 : ℝ) - Real.pi * Real.exp (1379 / 800 : ℝ) =
      -(Real.pi * Real.exp (1379 / 800 : ℝ) - (689 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (689 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (689 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1378_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (72268286966916463 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1378_endpointUpper :
    hpThetaJensenKernelEndpointUpper (689 / 800 : ℝ) (1379 / 1600 : ℝ) ≤ (804977 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1379 / 800 : ℝ)) (88051151139229551 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1379 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1378_product_upper
  have hD : (282693318145867371 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (689 / 400 : ℝ) - (1379 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1378_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1378_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (689 / 400 : ℝ) - (1379 / 3200 : ℝ)) ≤
      (1 / (282693318145867371 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (282693318145867371 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1379 / 3200 : ℝ) - Real.pi * Real.exp (689 / 400 : ℝ)) ≤
      (2 / (282693318145867371 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1379 / 3200 : ℝ) - Real.pi * Real.exp (689 / 400 : ℝ) =
      -(Real.pi * Real.exp (689 / 400 : ℝ) - (1379 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (88051151139229551 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (88051151139229551 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1378_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (689 / 800 : ℝ) (1379 / 1600 : ℝ)) :
    (783091 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (804977 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1378_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1378_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1379_leftExp :
    (14013774403 / 2500000000 : ℝ) ≤ Real.exp (1379 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1379 / 800 : ℝ) (527672214957 / 500000000000 : ℝ)
    (14013774403 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1379_rightExp :
    Real.exp (69 / 40 : ℝ) ≤ (28062605149 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (69 / 40 : ℝ) (131923206889 / 125000000000 : ℝ)
    (28062605149 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1379_denomUpper :
    Real.exp (86006596397862357 / 5000000000000000 : ℝ) ≤ (14770937105105143 / 500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (86006596397862357 / 5000000000000000 : ℝ) (106987048409
    / 62500000000 : ℝ) (14770937105105143 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1379_denomLower :
    (288890914015432863 / 10000000000 : ℝ) ≤ Real.exp (5368429569283697 / 312500000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (5368429569283697 / 312500000000000 : ℝ) (427649474317 /
    250000000000 : ℝ) (288890914015432863 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1379_product_lower :
    (5503195194283697 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (1379 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1379_leftExp
    (by norm_num : (0 : ℝ) ≤ (14013774403 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1379_product_upper :
    Real.pi * Real.exp (69 / 40 : ℝ) ≤ (88161283897862357 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1379_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1379_endpointLower :
    (384139 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1379 / 1600 : ℝ) (69 / 80 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5503195194283697 / 312500000000000 : ℝ) (Real.pi * Real.exp (1379 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1379_product_lower
  have hD : Real.exp (Real.pi * Real.exp (69 / 40 : ℝ) - (1379 / 3200 : ℝ)) ≤
      (14770937105105143 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1379_denomUpper
    linarith [hpThetaJensenCell1379_product_upper]
  have hi : (1 / (14770937105105143 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (69 / 40 : ℝ) - (1379 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (14770937105105143 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (14770937105105143 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1379 / 3200 : ℝ) - Real.pi * Real.exp (69 / 40 : ℝ)) := by
    rw [show (1379 / 3200 : ℝ) - Real.pi * Real.exp (69 / 40 : ℝ) =
      -(Real.pi * Real.exp (69 / 40 : ℝ) - (1379 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1379 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1379 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1379_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (14770937105105143 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1379_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1379 / 1600 : ℝ) (69 / 80 : ℝ) ≤ (197443 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (69 / 40 : ℝ)) (88161283897862357 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (69 / 80 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1379_product_upper
  have hD : (288890914015432863 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1379 / 800 : ℝ) - (69 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell1379_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1379_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1379 / 800 : ℝ) - (69 / 160 : ℝ)) ≤
      (1 / (288890914015432863 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (288890914015432863 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((69 / 160 : ℝ) - Real.pi * Real.exp (1379 / 800 : ℝ)) ≤
      (2 / (288890914015432863 / 10000000000 : ℝ) : ℝ) := by
    rw [show (69 / 160 : ℝ) - Real.pi * Real.exp (1379 / 800 : ℝ) =
      -(Real.pi * Real.exp (1379 / 800 : ℝ) - (69 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (88161283897862357 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (88161283897862357 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1379_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1379 / 1600 : ℝ) (69 / 80 : ℝ)) :
    (384139 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (197443 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1379_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1379_endpointUpper

def hpThetaJensenCellsBatch068Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (219833 / 2000000000 : ℝ)
  | 1 => (134863 / 1250000000 : ℝ)
  | 2 => (1058989 / 10000000000 : ℝ)
  | 3 => (259853 / 2500000000 : ℝ)
  | 4 => (102017 / 1000000000 : ℝ)
  | 5 => (1001257 / 10000000000 : ℝ)
  | 6 => (245667 / 2500000000 : ℝ)
  | 7 => (964397 / 10000000000 : ℝ)
  | 8 => (946441 / 10000000000 : ℝ)
  | 9 => (928793 / 10000000000 : ℝ)
  | 10 => (911449 / 10000000000 : ℝ)
  | 11 => (178881 / 2000000000 : ℝ)
  | 12 => (109707 / 1250000000 : ℝ)
  | 13 => (215299 / 2500000000 : ℝ)
  | 14 => (422511 / 5000000000 : ℝ)
  | 15 => (829129 / 10000000000 : ℝ)
  | 16 => (101689 / 1250000000 : ℝ)
  | 17 => (99771 / 1250000000 : ℝ)
  | 18 => (783091 / 10000000000 : ℝ)
  | 19 => (384139 / 5000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch068Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (225867 / 2000000000 : ℝ)
  | 1 => (277137 / 2500000000 : ℝ)
  | 2 => (544057 / 5000000000 : ℝ)
  | 3 => (267007 / 2500000000 : ℝ)
  | 4 => (209657 / 2000000000 : ℝ)
  | 5 => (514439 / 5000000000 : ℝ)
  | 6 => (1009803 / 10000000000 : ℝ)
  | 7 => (198211 / 2000000000 : ℝ)
  | 8 => (243157 / 2500000000 : ℝ)
  | 9 => (477259 / 5000000000 : ℝ)
  | 10 => (936719 / 10000000000 : ℝ)
  | 11 => (229807 / 2500000000 : ℝ)
  | 12 => (451019 / 5000000000 : ℝ)
  | 13 => (177029 / 2000000000 : ℝ)
  | 14 => (173709 / 2000000000 : ℝ)
  | 15 => (106529 / 1250000000 : ℝ)
  | 16 => (836203 / 10000000000 : ℝ)
  | 17 => (820453 / 10000000000 : ℝ)
  | 18 => (804977 / 10000000000 : ℝ)
  | 19 => (197443 / 2500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch068_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1360 : ℝ) + (j.val : ℝ)) / 1600)
      (((1360 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch068Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch068Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1360_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1361_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1362_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1363_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1364_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1365_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1366_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1367_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1368_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1369_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1370_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1371_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1372_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1373_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1374_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1375_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1376_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1377_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1378_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1379_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper] at h ⊢
    exact h

end HodgeProofHP
