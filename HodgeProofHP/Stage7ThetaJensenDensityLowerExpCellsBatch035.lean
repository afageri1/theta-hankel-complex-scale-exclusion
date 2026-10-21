/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityCurvatureExponentialCells

/-! Exact rational certificates with a full infinite-series remainder bound. -/
noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell700 :
    ∀ t ∈ Set.Icc ((43747 / 512000) : ℝ) (43763 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1186356349 / 1000000000) : ℝ) ≤ Real.exp (2 * (43747 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43747 / 512000)) (1186356349 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43763 / 512000) : ℝ)) ≤ (2372861 / 2000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43763 / 512000)) (2372861 / 2000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((71740714959 / 1000000) : ℝ) ≤ Real.exp (3 * (1863469 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1863469 / 500000)) (71740714959 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43747 / 512000) : ℝ) (43763 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1863469 / 500000) (3727291 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43747 / 512000) (43763 / 512000) (1186356349 / 1000000000) (2372861 / 2000000) (1863469 / 500000) (3727291 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43747 / 512000) (43763 / 512000) (1863469 / 500000) (3727291 / 1000000) (8299 / 250) (3321 / 100)
    (26631 / 500) (10693 / 200) (-278651 / 500) (185519 / 500000) (1544057 / 500) (3568407 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1863469 / 500000) (71740714959 / 1000000) (3568407 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1863469 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1863469 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell701 :
    ∀ t ∈ Set.Icc ((43763 / 512000) : ℝ) (43779 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1186430499 / 1000000000) : ℝ) ≤ Real.exp (2 * (43763 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43763 / 512000)) (1186430499 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43779 / 512000) : ℝ)) ≤ (593252327 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43779 / 512000)) (593252327 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((35895439611 / 500000) : ℝ) ≤ Real.exp (3 * (3727171 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3727171 / 1000000)) (35895439611 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43763 / 512000) : ℝ) (43779 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3727171 / 1000000) (931881 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43763 / 512000) (43779 / 512000) (1186430499 / 1000000000) (593252327 / 500000000) (3727171 / 1000000) (931881 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43763 / 512000) (43779 / 512000) (3727171 / 1000000) (931881 / 250000) (16601 / 500) (6643 / 200)
    (53291 / 1000) (26747 / 500) (-27867 / 50) (11589 / 31250) (1544443 / 500) (3565913 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3727171 / 1000000) (35895439611 / 500000) (3565913 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3727171 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3727171 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell702 :
    ∀ t ∈ Set.Icc ((43779 / 512000) : ℝ) (8759 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1186504653 / 1000000000) : ℝ) ≤ Real.exp (2 * (43779 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43779 / 512000)) (1186504653 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8759 / 102400) : ℝ)) ≤ (1186578813 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8759 / 102400)) (1186578813 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((35920539281 / 500000) : ℝ) ≤ Real.exp (3 * (931851 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (931851 / 250000)) (35920539281 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43779 / 512000) : ℝ) (8759 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (931851 / 250000) (931939 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43779 / 512000) (8759 / 102400) (1186504653 / 1000000000) (1186578813 / 1000000000) (931851 / 250000) (931939 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43779 / 512000) (8759 / 102400) (931851 / 250000) (931939 / 250000) (33207 / 1000) (33221 / 1000)
    (1333 / 25) (53523 / 1000) (-278691 / 500) (185329 / 500000) (617931 / 200) (3563421 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (931851 / 250000) (35920539281 / 500000) (3563421 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (931851 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (931851 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell703 :
    ∀ t ∈ Set.Icc ((8759 / 102400) : ℝ) (43811 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((296644703 / 250000000) : ℝ) ≤ Real.exp (2 * (8759 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8759 / 102400)) (296644703 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43811 / 512000) : ℝ)) ≤ (74165811 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43811 / 512000)) (74165811 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((17972828251 / 250000) : ℝ) ≤ Real.exp (3 * (3727637 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3727637 / 1000000)) (17972828251 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8759 / 102400) : ℝ) (43811 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3727637 / 1000000) (3727989 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8759 / 102400) (43811 / 512000) (296644703 / 250000000) (74165811 / 62500000) (3727637 / 1000000) (3727989 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8759 / 102400) (43811 / 512000) (3727637 / 1000000) (3727989 / 1000000) (33213 / 1000) (16613 / 500)
    (53349 / 1000) (6694 / 125) (-557419 / 1000) (370469 / 1000000) (3090427 / 1000) (3560931 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3727637 / 1000000) (17972828251 / 250000) (3560931 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3727637 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3727637 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell704 :
    ∀ t ∈ Set.Icc ((43811 / 512000) : ℝ) (43827 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((47466119 / 40000000) : ℝ) ≤ Real.exp (2 * (43811 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43811 / 512000)) (47466119 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43827 / 512000) : ℝ)) ≤ (148340893 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43827 / 512000)) (148340893 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((71941582571 / 1000000) : ℝ) ≤ Real.exp (3 * (372787 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (372787 / 100000)) (71941582571 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43811 / 512000) : ℝ) (43827 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (372787 / 100000) (1864111 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43811 / 512000) (43827 / 512000) (47466119 / 40000000) (148340893 / 125000000) (372787 / 100000) (1864111 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43811 / 512000) (43827 / 512000) (372787 / 100000) (1864111 / 500000) (16609 / 500) (4154 / 125)
    (26689 / 500) (53581 / 1000) (-69682 / 125) (370279 / 1000000) (15456 / 5) (3558443 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (372787 / 100000) (71941582571 / 1000000) (3558443 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (372787 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (372787 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell705 :
    ∀ t ∈ Set.Icc ((43827 / 512000) : ℝ) (43843 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1186727143 / 1000000000) : ℝ) ≤ Real.exp (2 * (43827 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43827 / 512000)) (1186727143 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43843 / 512000) : ℝ)) ≤ (1186801317 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43843 / 512000)) (1186801317 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((7199188729 / 100000) : ℝ) ≤ Real.exp (3 * (3728103 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3728103 / 1000000)) (7199188729 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43827 / 512000) : ℝ) (43843 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3728103 / 1000000) (466057 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43827 / 512000) (43843 / 512000) (1186727143 / 1000000000) (1186801317 / 1000000000) (3728103 / 1000000) (466057 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43827 / 512000) (43843 / 512000) (3728103 / 1000000) (466057 / 125000) (4153 / 125) (33237 / 1000)
    (53407 / 1000) (5361 / 100) (-557489 / 1000) (37009 / 100000) (386497 / 125) (3555957 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3728103 / 1000000) (7199188729 / 100000) (3555957 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3728103 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3728103 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell706 :
    ∀ t ∈ Set.Icc ((43843 / 512000) : ℝ) (43859 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((296700329 / 250000000) : ℝ) ≤ Real.exp (2 * (43843 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43843 / 512000)) (296700329 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43859 / 512000) : ℝ)) ≤ (593437747 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43859 / 512000)) (593437747 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((72042227183 / 1000000) : ℝ) ≤ Real.exp (3 * (233021 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (233021 / 62500)) (72042227183 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43843 / 512000) : ℝ) (43859 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (233021 / 62500) (3728689 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43843 / 512000) (43859 / 512000) (296700329 / 250000000) (593437747 / 500000000) (233021 / 62500) (3728689 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43843 / 512000) (43859 / 512000) (233021 / 62500) (3728689 / 1000000) (33229 / 1000) (33243 / 1000)
    (13359 / 250) (53639 / 1000) (-278763 / 500) (369901 / 1000000) (3092749 / 1000) (55523 / 15625000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (233021 / 62500) (72042227183 / 1000000) (55523 / 15625000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (233021 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (233021 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell707 :
    ∀ t ∈ Set.Icc ((43859 / 512000) : ℝ) (351 / 4096), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1186875493 / 1000000000) : ℝ) ≤ Real.exp (2 * (43859 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43859 / 512000)) (1186875493 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((351 / 4096) : ℝ)) ≤ (296737419 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (351 / 4096)) (296737419 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((72092602277 / 1000000) : ℝ) ≤ Real.exp (3 * (3728569 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3728569 / 1000000)) (72092602277 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43859 / 512000) : ℝ) (351 / 4096),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3728569 / 1000000) (1864461 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43859 / 512000) (351 / 4096) (1186875493 / 1000000000) (296737419 / 250000000) (3728569 / 1000000) (1864461 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43859 / 512000) (351 / 4096) (3728569 / 1000000) (1864461 / 500000) (6647 / 200) (33249 / 1000)
    (26733 / 500) (53669 / 1000) (-557563 / 1000) (23107 / 62500) (1546761 / 500) (3550989 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3728569 / 1000000) (72092602277 / 1000000) (3550989 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3728569 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3728569 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell708 :
    ∀ t ∈ Set.Icc ((351 / 4096) : ℝ) (43891 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((47477987 / 40000000) : ℝ) ≤ Real.exp (2 * (351 / 4096)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (351 / 4096)) (47477987 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43891 / 512000) : ℝ)) ≤ (1187023863 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43891 / 512000)) (1187023863 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((14428602519 / 200000) : ℝ) ≤ Real.exp (3 * (1864401 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1864401 / 500000)) (14428602519 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((351 / 4096) : ℝ) (43891 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1864401 / 500000) (745831 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (351 / 4096) (43891 / 512000) (47477987 / 40000000) (1187023863 / 1000000000) (1864401 / 500000) (745831 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (351 / 4096) (43891 / 512000) (1864401 / 500000) (745831 / 200000) (831 / 25) (16627 / 500)
    (10699 / 200) (26849 / 500) (-557601 / 1000) (369523 / 1000000) (386787 / 125) (887127 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1864401 / 500000) (14428602519 / 200000) (887127 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1864401 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1864401 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell709 :
    ∀ t ∈ Set.Icc ((43891 / 512000) : ℝ) (43907 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((593511931 / 500000000) : ℝ) ≤ Real.exp (2 * (43891 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43891 / 512000)) (593511931 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43907 / 512000) : ℝ)) ≤ (593549027 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43907 / 512000)) (593549027 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((36096729081 / 500000) : ℝ) ≤ Real.exp (3 * (745807 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (745807 / 200000)) (36096729081 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43891 / 512000) : ℝ) (43907 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (745807 / 200000) (932347 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43891 / 512000) (43907 / 512000) (593511931 / 500000000) (593549027 / 500000000) (745807 / 200000) (932347 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43891 / 512000) (43907 / 512000) (745807 / 200000) (932347 / 250000) (16623 / 500) (1663 / 50)
    (13381 / 250) (53727 / 1000) (-278819 / 500) (184667 / 500000) (3095069 / 1000) (886507 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (745807 / 200000) (36096729081 / 500000) (886507 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (745807 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (745807 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell710 :
    ∀ t ∈ Set.Icc ((43907 / 512000) : ℝ) (43923 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1187098053 / 1000000000) : ℝ) ≤ Real.exp (2 * (43907 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43907 / 512000)) (1187098053 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43923 / 512000) : ℝ)) ≤ (4748689 / 4000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43923 / 512000)) (4748689 / 4000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((36121969501 / 500000) : ℝ) ≤ Real.exp (3 * (932317 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (932317 / 250000)) (36121969501 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43907 / 512000) : ℝ) (43923 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (932317 / 250000) (3729621 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43907 / 512000) (43923 / 512000) (1187098053 / 1000000000) (4748689 / 4000000) (932317 / 250000) (3729621 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43907 / 512000) (43923 / 512000) (932317 / 250000) (3729621 / 1000000) (8313 / 250) (6653 / 200)
    (53553 / 1000) (13439 / 250) (-22307 / 40) (73829 / 200000) (3095843 / 1000) (70871 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (932317 / 250000) (36121969501 / 500000) (70871 / 20000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (932317 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (932317 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell711 :
    ∀ t ∈ Set.Icc ((43923 / 512000) : ℝ) (43939 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1187172249 / 1000000000) : ℝ) ≤ Real.exp (2 * (43923 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43923 / 512000)) (1187172249 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43939 / 512000) : ℝ)) ≤ (1187246451 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43939 / 512000)) (1187246451 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((72294455141 / 1000000) : ℝ) ≤ Real.exp (3 * (3729501 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3729501 / 1000000)) (72294455141 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43923 / 512000) : ℝ) (43939 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3729501 / 1000000) (1864927 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43923 / 512000) (43939 / 512000) (1187172249 / 1000000000) (1187246451 / 1000000000) (3729501 / 1000000) (1864927 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43923 / 512000) (43939 / 512000) (3729501 / 1000000) (1864927 / 500000) (33257 / 1000) (33271 / 1000)
    (26791 / 500) (10757 / 200) (-69714 / 125) (92239 / 250000) (387077 / 125) (1770537 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3729501 / 1000000) (72294455141 / 1000000) (1770537 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3729501 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3729501 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell712 :
    ∀ t ∈ Set.Icc ((43939 / 512000) : ℝ) (8791 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((23744929 / 20000000) : ℝ) ≤ Real.exp (2 * (43939 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43939 / 512000)) (23744929 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8791 / 102400) : ℝ)) ≤ (74207541 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8791 / 102400)) (74207541 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((18086251651 / 250000) : ℝ) ≤ Real.exp (3 * (1864867 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1864867 / 500000)) (18086251651 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43939 / 512000) : ℝ) (8791 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1864867 / 500000) (3730087 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43939 / 512000) (8791 / 102400) (23744929 / 20000000) (74207541 / 62500000) (1864867 / 500000) (3730087 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43939 / 512000) (8791 / 102400) (1864867 / 500000) (3730087 / 1000000) (33263 / 1000) (8319 / 250)
    (53611 / 1000) (26907 / 500) (-557749 / 1000) (5762 / 15625) (309739 / 100) (17693 / 5000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1864867 / 500000) (18086251651 / 250000) (17693 / 5000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1864867 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1864867 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell713 :
    ∀ t ∈ Set.Icc ((8791 / 102400) : ℝ) (43971 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((237464131 / 200000000) : ℝ) ≤ Real.exp (2 * (8791 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8791 / 102400)) (237464131 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43971 / 512000) : ℝ)) ≤ (593697433 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43971 / 512000)) (593697433 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((36197796707 / 500000) : ℝ) ≤ Real.exp (3 * (3729967 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3729967 / 1000000)) (36197796707 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8791 / 102400) : ℝ) (43971 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3729967 / 1000000) (46629 / 12500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8791 / 102400) (43971 / 512000) (237464131 / 200000000) (593697433 / 500000000) (3729967 / 1000000) (46629 / 12500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8791 / 102400) (43971 / 512000) (3729967 / 1000000) (46629 / 12500) (8317 / 250) (16641 / 500)
    (1341 / 25) (53843 / 1000) (-278893 / 500) (368579 / 1000000) (774541 / 250) (3536127 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3729967 / 1000000) (36197796707 / 500000) (3536127 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3729967 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3729967 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell714 :
    ∀ t ∈ Set.Icc ((43971 / 512000) : ℝ) (43987 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((237478973 / 200000000) : ℝ) ≤ Real.exp (2 * (43971 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43971 / 512000)) (237478973 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43987 / 512000) : ℝ)) ≤ (1187469081 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43987 / 512000)) (1187469081 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((18111553899 / 250000) : ℝ) ≤ Real.exp (3 * (18651 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (18651 / 5000)) (18111553899 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43971 / 512000) : ℝ) (43987 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (18651 / 5000) (3730553 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43971 / 512000) (43987 / 512000) (237478973 / 200000000) (1187469081 / 1000000000) (18651 / 5000) (3730553 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43971 / 512000) (43987 / 512000) (18651 / 5000) (3730553 / 1000000) (16637 / 500) (33287 / 1000)
    (53669 / 1000) (53873 / 1000) (-557823 / 1000) (36839 / 100000) (1549469 / 500) (441707 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (18651 / 5000) (18111553899 / 250000) (441707 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (18651 / 5000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (18651 / 5000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell715 :
    ∀ t ∈ Set.Icc ((43987 / 512000) : ℝ) (44003 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((29686727 / 25000000) : ℝ) ≤ Real.exp (2 * (43987 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43987 / 512000)) (29686727 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44003 / 512000) : ℝ)) ≤ (11875433 / 10000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44003 / 512000)) (11875433 / 10000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((36248545333 / 500000) : ℝ) ≤ Real.exp (3 * (1865217 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1865217 / 500000)) (36248545333 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43987 / 512000) : ℝ) (44003 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1865217 / 500000) (3730787 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43987 / 512000) (44003 / 512000) (29686727 / 25000000) (11875433 / 10000000) (1865217 / 500000) (3730787 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43987 / 512000) (44003 / 512000) (1865217 / 500000) (3730787 / 1000000) (33279 / 1000) (33293 / 1000)
    (53699 / 1000) (26951 / 500) (-27893 / 50) (368201 / 1000000) (774929 / 250) (3531177 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1865217 / 500000) (36248545333 / 500000) (3531177 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1865217 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1865217 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell716 :
    ∀ t ∈ Set.Icc ((44003 / 512000) : ℝ) (44019 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1187543299 / 1000000000) : ℝ) ≤ Real.exp (2 * (44003 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44003 / 512000)) (1187543299 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44019 / 512000) : ℝ)) ≤ (1187617523 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44019 / 512000)) (1187617523 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3627389191 / 50000) : ℝ) ≤ Real.exp (3 * (3730667 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3730667 / 1000000)) (3627389191 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44003 / 512000) : ℝ) (44019 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3730667 / 1000000) (186551 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44003 / 512000) (44019 / 512000) (1187543299 / 1000000000) (1187617523 / 1000000000) (3730667 / 1000000) (186551 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44003 / 512000) (44019 / 512000) (3730667 / 1000000) (186551 / 50000) (6657 / 200) (33299 / 1000)
    (6716 / 125) (53931 / 1000) (-557897 / 1000) (368013 / 1000000) (310049 / 100) (3528709 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3730667 / 1000000) (3627389191 / 50000) (3528709 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3730667 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3730667 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell717 :
    ∀ t ∈ Set.Icc ((44019 / 512000) : ℝ) (8807 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((593808761 / 500000000) : ℝ) ≤ Real.exp (2 * (44019 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44019 / 512000)) (593808761 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8807 / 102400) : ℝ)) ≤ (148461469 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8807 / 102400)) (148461469 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((72598512421 / 1000000) : ℝ) ≤ Real.exp (3 * (37309 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (37309 / 10000)) (72598512421 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44019 / 512000) : ℝ) (8807 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (37309 / 10000) (3731253 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44019 / 512000) (8807 / 102400) (593808761 / 500000000) (148461469 / 125000000) (37309 / 10000) (3731253 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44019 / 512000) (8807 / 102400) (37309 / 10000) (3731253 / 1000000) (3329 / 100) (4163 / 125)
    (53757 / 1000) (1349 / 25) (-278967 / 500) (14713 / 40000) (620253 / 200) (881561 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (37309 / 10000) (72598512421 / 1000000) (881561 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (37309 / 10000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (37309 / 10000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell718 :
    ∀ t ∈ Set.Icc ((8807 / 102400) : ℝ) (44051 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1187691751 / 1000000000) : ℝ) ≤ Real.exp (2 * (8807 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8807 / 102400)) (1187691751 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44051 / 512000) : ℝ)) ≤ (237553197 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44051 / 512000)) (237553197 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((72649276493 / 1000000) : ℝ) ≤ Real.exp (3 * (3731133 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3731133 / 1000000)) (72649276493 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8807 / 102400) : ℝ) (44051 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3731133 / 1000000) (1865743 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8807 / 102400) (44051 / 512000) (1187691751 / 1000000000) (237553197 / 200000000) (3731133 / 1000000) (1865743 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8807 / 102400) (44051 / 512000) (3731133 / 1000000) (1865743 / 500000) (4162 / 125) (3331 / 100)
    (26893 / 500) (5399 / 100) (-557971 / 1000) (91909 / 250000) (3102039 / 1000) (176189 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3731133 / 1000000) (72649276493 / 1000000) (176189 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3731133 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3731133 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell719 :
    ∀ t ∈ Set.Icc ((44051 / 512000) : ℝ) (44067 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((37117687 / 31250000) : ℝ) ≤ Real.exp (2 * (44051 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44051 / 512000)) (37117687 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44067 / 512000) : ℝ)) ≤ (1187840223 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44067 / 512000)) (1187840223 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((72700076061 / 1000000) : ℝ) ≤ Real.exp (3 * (1865683 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1865683 / 500000)) (72700076061 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44051 / 512000) : ℝ) (44067 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1865683 / 500000) (3731719 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44051 / 512000) (44067 / 512000) (37117687 / 31250000) (1187840223 / 1000000000) (1865683 / 500000) (3731719 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44051 / 512000) (44067 / 512000) (1865683 / 500000) (3731719 / 1000000) (16651 / 500) (6663 / 200)
    (10763 / 200) (54019 / 1000) (-69751 / 125) (45931 / 125000) (1551407 / 500) (3521317 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1865683 / 500000) (72700076061 / 1000000) (3521317 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1865683 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1865683 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch035 :
    ∀ t ∈ Set.Icc ((43747 / 512000) : ℝ) (44067 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell700
      hpThetaDensityLowerExpCompact_cell701)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell702
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell703
      hpThetaDensityLowerExpCompact_cell704)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell705
      hpThetaDensityLowerExpCompact_cell706)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell707
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell708
      hpThetaDensityLowerExpCompact_cell709))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell710
      hpThetaDensityLowerExpCompact_cell711)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell712
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell713
      hpThetaDensityLowerExpCompact_cell714)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell715
      hpThetaDensityLowerExpCompact_cell716)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell717
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell718
      hpThetaDensityLowerExpCompact_cell719)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch035
end HodgeProofHP
