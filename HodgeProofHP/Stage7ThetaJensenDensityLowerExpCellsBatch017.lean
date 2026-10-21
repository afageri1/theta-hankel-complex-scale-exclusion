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
theorem hpThetaDensityLowerExpCompact_cell340 :
    ∀ t ∈ Set.Icc ((41499 / 512000) : ℝ) (41503 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((146998033 / 125000000) : ℝ) ≤ Real.exp (2 * (41499 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41499 / 512000)) (146998033 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41503 / 512000) : ℝ)) ≤ (14700033 / 12500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41503 / 512000)) (14700033 / 12500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65059776543 / 1000000) : ℝ) ≤ Real.exp (3 * (1847177 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1847177 / 500000)) (65059776543 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41499 / 512000) : ℝ) (41503 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1847177 / 500000) (369453 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41499 / 512000) (41503 / 512000) (146998033 / 125000000) (14700033 / 12500000) (1847177 / 500000) (369453 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41499 / 512000) (41503 / 512000) (1847177 / 500000) (369453 / 100000) (1297 / 40) (32433 / 1000)
    (493 / 10) (247 / 5) (-276301 / 500) (199223 / 500000) (596193 / 200) (3934843 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1847177 / 500000) (65059776543 / 1000000) (3934843 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1847177 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1847177 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell341 :
    ∀ t ∈ Set.Icc ((41503 / 512000) : ℝ) (41507 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1176002639 / 1000000000) : ℝ) ≤ Real.exp (2 * (41503 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41503 / 512000)) (1176002639 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41507 / 512000) : ℝ)) ≤ (235204203 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41507 / 512000)) (235204203 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16267774481 / 250000) : ℝ) ≤ Real.exp (3 * (923603 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (923603 / 250000)) (16267774481 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41503 / 512000) : ℝ) (41507 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (923603 / 250000) (923647 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41503 / 512000) (41507 / 512000) (1176002639 / 1000000000) (235204203 / 200000000) (923603 / 250000) (923647 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41503 / 512000) (41507 / 512000) (923603 / 250000) (923647 / 250000) (32427 / 1000) (16217 / 500)
    (49307 / 1000) (49407 / 1000) (-552613 / 1000) (79679 / 200000) (372644 / 125) (3934159 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (923603 / 250000) (16267774481 / 250000) (3934159 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (923603 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (923603 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell342 :
    ∀ t ∈ Set.Icc ((41507 / 512000) : ℝ) (41511 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((588010507 / 500000000) : ℝ) ≤ Real.exp (2 * (41507 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41507 / 512000)) (588010507 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41511 / 512000) : ℝ)) ≤ (117603939 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41511 / 512000)) (117603939 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2603296851 / 40000) : ℝ) ≤ Real.exp (3 * (369447 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (369447 / 100000)) (2603296851 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41507 / 512000) : ℝ) (41511 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (369447 / 100000) (1847323 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41507 / 512000) (41511 / 512000) (588010507 / 500000000) (117603939 / 100000000) (369447 / 100000) (1847323 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41507 / 512000) (41511 / 512000) (369447 / 100000) (1847323 / 500000) (8107 / 250) (6487 / 200)
    (24657 / 500) (24707 / 500) (-552623 / 1000) (79669 / 200000) (2981339 / 1000) (1966737 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (369447 / 100000) (2603296851 / 40000) (1966737 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (369447 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (369447 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell343 :
    ∀ t ∈ Set.Icc ((41511 / 512000) : ℝ) (8303 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1176039389 / 1000000000) : ℝ) ≤ Real.exp (2 * (41511 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41511 / 512000)) (1176039389 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8303 / 102400) : ℝ)) ≤ (588028883 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8303 / 102400)) (588028883 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16273387829 / 250000) : ℝ) ≤ Real.exp (3 * (3694527 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3694527 / 1000000)) (16273387829 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41511 / 512000) : ℝ) (8303 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3694527 / 1000000) (230919 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41511 / 512000) (8303 / 102400) (1176039389 / 1000000000) (588028883 / 500000000) (3694527 / 1000000) (230919 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41511 / 512000) (8303 / 102400) (3694527 / 1000000) (230919 / 62500) (32429 / 1000) (32437 / 1000)
    (49321 / 1000) (24711 / 500) (-138157 / 250) (79659 / 200000) (1490763 / 500) (1966401 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3694527 / 1000000) (16273387829 / 250000) (1966401 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3694527 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3694527 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell344 :
    ∀ t ∈ Set.Icc ((8303 / 102400) : ℝ) (41519 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235211553 / 200000000) : ℝ) ≤ Real.exp (2 * (8303 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8303 / 102400)) (235211553 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41519 / 512000) : ℝ)) ≤ (588038071 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41519 / 512000)) (588038071 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32552439287 / 500000) : ℝ) ≤ Real.exp (3 * (738917 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (738917 / 200000)) (32552439287 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8303 / 102400) : ℝ) (41519 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (738917 / 200000) (3694761 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8303 / 102400) (41519 / 512000) (235211553 / 200000000) (588038071 / 500000000) (738917 / 200000) (3694761 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8303 / 102400) (41519 / 512000) (738917 / 200000) (3694761 / 1000000) (32431 / 1000) (16219 / 500)
    (6166 / 125) (12357 / 250) (-552643 / 1000) (79649 / 200000) (298171 / 100) (1966059 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (738917 / 200000) (32552439287 / 500000) (1966059 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (738917 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (738917 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell345 :
    ∀ t ∈ Set.Icc ((41519 / 512000) : ℝ) (41523 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1176076141 / 1000000000) : ℝ) ≤ Real.exp (2 * (41519 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41519 / 512000)) (1176076141 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41523 / 512000) : ℝ)) ≤ (1176094519 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41523 / 512000)) (1176094519 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16279051951 / 250000) : ℝ) ≤ Real.exp (3 * (3694643 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3694643 / 1000000)) (16279051951 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41519 / 512000) : ℝ) (41523 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3694643 / 1000000) (3694819 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41519 / 512000) (41523 / 512000) (1176076141 / 1000000000) (1176094519 / 1000000000) (3694643 / 1000000) (3694819 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41519 / 512000) (41523 / 512000) (3694643 / 1000000) (3694819 / 1000000) (4054 / 125) (32439 / 1000)
    (9867 / 200) (9887 / 200) (-552653 / 1000) (199097 / 500000) (1490949 / 500) (3931433 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3694643 / 1000000) (16279051951 / 250000) (3931433 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3694643 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3694643 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell346 :
    ∀ t ∈ Set.Icc ((41523 / 512000) : ℝ) (41527 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((588047259 / 500000000) : ℝ) ≤ Real.exp (2 * (41523 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41523 / 512000)) (588047259 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41527 / 512000) : ℝ)) ≤ (235222579 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41527 / 512000)) (235222579 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32563671811 / 500000) : ℝ) ≤ Real.exp (3 * (36947 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (36947 / 10000)) (32563671811 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41523 / 512000) : ℝ) (41527 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (36947 / 10000) (3694877 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41523 / 512000) (41527 / 512000) (588047259 / 500000000) (235222579 / 200000000) (36947 / 10000) (3694877 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41523 / 512000) (41527 / 512000) (36947 / 10000) (3694877 / 1000000) (32433 / 1000) (32441 / 1000)
    (24671 / 500) (49443 / 1000) (-552659 / 1000) (79629 / 200000) (596417 / 200) (3930761 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (36947 / 10000) (32563671811 / 500000) (3930761 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (36947 / 10000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (36947 / 10000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell347 :
    ∀ t ∈ Set.Icc ((41527 / 512000) : ℝ) (41531 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((588056447 / 500000000) : ℝ) ≤ Real.exp (2 * (41527 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41527 / 512000)) (588056447 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41531 / 512000) : ℝ)) ≤ (147016409 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41531 / 512000)) (147016409 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65138676761 / 1000000) : ℝ) ≤ Real.exp (3 * (1847379 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1847379 / 500000)) (65138676761 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41527 / 512000) : ℝ) (41531 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1847379 / 500000) (738987 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41527 / 512000) (41531 / 512000) (588056447 / 500000000) (147016409 / 125000000) (1847379 / 500000) (738987 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41527 / 512000) (41531 / 512000) (1847379 / 500000) (738987 / 200000) (6487 / 200) (16221 / 500)
    (49349 / 1000) (989 / 20) (-552669 / 1000) (199047 / 500000) (372784 / 125) (3930077 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1847379 / 500000) (65138676761 / 1000000) (3930077 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1847379 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1847379 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell348 :
    ∀ t ∈ Set.Icc ((41531 / 512000) : ℝ) (8307 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1176131271 / 1000000000) : ℝ) ≤ Real.exp (2 * (41531 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41531 / 512000)) (1176131271 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8307 / 102400) : ℝ)) ≤ (1176149649 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8307 / 102400)) (1176149649 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65150011871 / 1000000) : ℝ) ≤ Real.exp (3 * (115463 / 31250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (115463 / 31250)) (65150011871 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41531 / 512000) : ℝ) (8307 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (115463 / 31250) (230937 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41531 / 512000) (8307 / 102400) (1176131271 / 1000000000) (1176149649 / 1000000000) (115463 / 31250) (230937 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41531 / 512000) (8307 / 102400) (115463 / 31250) (230937 / 62500) (8109 / 250) (32443 / 1000)
    (12339 / 250) (6182 / 125) (-138171 / 250) (398043 / 1000000) (372807 / 125) (3929393 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (115463 / 31250) (65150011871 / 1000000) (3929393 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (115463 / 31250)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (115463 / 31250)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell349 :
    ∀ t ∈ Set.Icc ((8307 / 102400) : ℝ) (41539 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((73509353 / 62500000) : ℝ) ≤ Real.exp (2 * (8307 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8307 / 102400)) (73509353 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41539 / 512000) : ℝ)) ≤ (1176168027 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41539 / 512000)) (1176168027 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13032269791 / 200000) : ℝ) ≤ Real.exp (3 * (1847437 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1847437 / 500000)) (13032269791 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8307 / 102400) : ℝ) (41539 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1847437 / 500000) (73901 / 20000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8307 / 102400) (41539 / 512000) (73509353 / 62500000) (1176168027 / 1000000000) (1847437 / 500000) (73901 / 20000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8307 / 102400) (41539 / 512000) (1847437 / 500000) (73901 / 20000) (16219 / 500) (6489 / 200)
    (49363 / 1000) (49463 / 1000) (-276347 / 500) (397993 / 1000000) (2982643 / 1000) (392871 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1847437 / 500000) (13032269791 / 200000) (392871 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1847437 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1847437 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell350 :
    ∀ t ∈ Set.Icc ((41539 / 512000) : ℝ) (41543 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((588084013 / 500000000) : ℝ) ≤ Real.exp (2 * (41539 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41539 / 512000)) (588084013 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41543 / 512000) : ℝ)) ≤ (235237281 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41543 / 512000)) (235237281 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65172492493 / 1000000) : ℝ) ≤ Real.exp (3 * (3694931 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3694931 / 1000000)) (65172492493 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41539 / 512000) : ℝ) (41543 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3694931 / 1000000) (923777 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41539 / 512000) (41543 / 512000) (588084013 / 500000000) (235237281 / 200000000) (3694931 / 1000000) (923777 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41539 / 512000) (41543 / 512000) (3694931 / 1000000) (923777 / 250000) (32439 / 1000) (16223 / 500)
    (4937 / 100) (4947 / 100) (-5527 / 10) (397943 / 1000000) (2982831 / 1000) (1964019 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3694931 / 1000000) (65172492493 / 1000000) (1964019 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3694931 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3694931 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell351 :
    ∀ t ∈ Set.Icc ((41543 / 512000) : ℝ) (41547 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((294046601 / 250000000) : ℝ) ≤ Real.exp (2 * (41543 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41543 / 512000)) (294046601 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41547 / 512000) : ℝ)) ≤ (1176204783 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41547 / 512000)) (1176204783 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4073989593 / 62500) : ℝ) ≤ Real.exp (3 * (3694989 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3694989 / 1000000)) (4073989593 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41543 / 512000) : ℝ) (41547 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3694989 / 1000000) (739033 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41543 / 512000) (41547 / 512000) (294046601 / 250000000) (1176204783 / 1000000000) (3694989 / 1000000) (739033 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41543 / 512000) (41547 / 512000) (3694989 / 1000000) (739033 / 200000) (811 / 25) (4056 / 125)
    (49377 / 1000) (49477 / 1000) (-276357 / 500) (397893 / 1000000) (596603 / 200) (785471 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3694989 / 1000000) (4073989593 / 62500) (785471 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3694989 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3694989 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell352 :
    ∀ t ∈ Set.Icc ((41547 / 512000) : ℝ) (41551 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((588102391 / 500000000) : ℝ) ≤ Real.exp (2 * (41547 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41547 / 512000)) (588102391 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41551 / 512000) : ℝ)) ≤ (1176223161 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41551 / 512000)) (1176223161 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65195176457 / 1000000) : ℝ) ≤ Real.exp (3 * (3695047 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3695047 / 1000000)) (65195176457 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41547 / 512000) : ℝ) (41551 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3695047 / 1000000) (3695223 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41547 / 512000) (41551 / 512000) (588102391 / 500000000) (1176223161 / 1000000000) (3695047 / 1000000) (3695223 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41547 / 512000) (41551 / 512000) (3695047 / 1000000) (3695223 / 1000000) (16221 / 500) (32449 / 1000)
    (6173 / 125) (12371 / 250) (-22109 / 40) (198921 / 500000) (1491601 / 500) (3926671 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3695047 / 1000000) (65195176457 / 1000000) (3926671 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3695047 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3695047 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell353 :
    ∀ t ∈ Set.Icc ((41551 / 512000) : ℝ) (8311 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((29405579 / 25000000) : ℝ) ≤ Real.exp (2 * (41551 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41551 / 512000)) (29405579 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8311 / 102400) : ℝ)) ≤ (58812077 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8311 / 102400)) (58812077 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65206521399 / 1000000) : ℝ) ≤ Real.exp (3 * (739021 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (739021 / 200000)) (65206521399 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41551 / 512000) : ℝ) (8311 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (739021 / 200000) (3695281 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41551 / 512000) (8311 / 102400) (29405579 / 25000000) (58812077 / 50000000) (739021 / 200000) (3695281 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41551 / 512000) (8311 / 102400) (739021 / 200000) (3695281 / 1000000) (32443 / 1000) (649 / 20)
    (49391 / 1000) (49491 / 1000) (-110547 / 200) (12431 / 31250) (2983389 / 1000) (981497 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (739021 / 200000) (65206521399 / 1000000) (981497 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (739021 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (739021 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell354 :
    ∀ t ∈ Set.Icc ((8311 / 102400) : ℝ) (41559 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1176241539 / 1000000000) : ℝ) ≤ Real.exp (2 * (8311 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8311 / 102400)) (1176241539 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41559 / 512000) : ℝ)) ≤ (588129959 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41559 / 512000)) (588129959 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65217672663 / 1000000) : ℝ) ≤ Real.exp (3 * (1847581 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1847581 / 500000)) (65217672663 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8311 / 102400) : ℝ) (41559 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1847581 / 500000) (3695339 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8311 / 102400) (41559 / 512000) (1176241539 / 1000000000) (588129959 / 500000000) (1847581 / 500000) (3695339 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8311 / 102400) (41559 / 512000) (1847581 / 500000) (3695339 / 1000000) (8111 / 250) (8113 / 250)
    (24699 / 500) (24749 / 500) (-27637 / 50) (198871 / 500000) (2983577 / 1000) (3925317 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1847581 / 500000) (65217672663 / 1000000) (3925317 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1847581 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1847581 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell355 :
    ∀ t ∈ Set.Icc ((41559 / 512000) : ℝ) (41563 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1176259917 / 1000000000) : ℝ) ≤ Real.exp (2 * (41559 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41559 / 512000)) (1176259917 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41563 / 512000) : ℝ)) ≤ (588139149 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41563 / 512000)) (588139149 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((815362769 / 12500) : ℝ) ≤ Real.exp (3 * (184761 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (184761 / 50000)) (815362769 / 12500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41559 / 512000) : ℝ) (41563 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (184761 / 50000) (923849 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41559 / 512000) (41563 / 512000) (1176259917 / 1000000000) (588139149 / 500000000) (184761 / 50000) (923849 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41559 / 512000) (41563 / 512000) (184761 / 50000) (923849 / 250000) (16223 / 500) (32453 / 1000)
    (9881 / 200) (9901 / 200) (-110551 / 200) (99423 / 250000) (2983761 / 1000) (1962317 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (184761 / 50000) (815362769 / 12500) (1962317 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (184761 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (184761 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell356 :
    ∀ t ∈ Set.Icc ((41563 / 512000) : ℝ) (41567 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1176278297 / 1000000000) : ℝ) ≤ Real.exp (2 * (41563 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41563 / 512000)) (1176278297 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41567 / 512000) : ℝ)) ≤ (1176296677 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41567 / 512000)) (1176296677 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1019380818 / 15625) : ℝ) ≤ Real.exp (3 * (1847639 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1847639 / 500000)) (1019380818 / 15625) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41563 / 512000) : ℝ) (41567 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1847639 / 500000) (1847727 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41563 / 512000) (41567 / 512000) (1176278297 / 1000000000) (1176296677 / 1000000000) (1847639 / 500000) (1847727 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41563 / 512000) (41567 / 512000) (1847639 / 500000) (1847727 / 500000) (32447 / 1000) (16227 / 500)
    (12353 / 250) (6189 / 125) (-110553 / 200) (397641 / 1000000) (745987 / 250) (3923951 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1847639 / 500000) (1019380818 / 15625) (3923951 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1847639 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1847639 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell357 :
    ∀ t ∈ Set.Icc ((41567 / 512000) : ℝ) (41571 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((294074169 / 250000000) : ℝ) ≤ Real.exp (2 * (41567 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41567 / 512000)) (294074169 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41571 / 512000) : ℝ)) ≤ (1176315057 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41571 / 512000)) (1176315057 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65251725159 / 1000000) : ℝ) ≤ Real.exp (3 * (461917 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (461917 / 125000)) (65251725159 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41567 / 512000) : ℝ) (41571 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (461917 / 125000) (461939 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41567 / 512000) (41571 / 512000) (294074169 / 250000000) (1176315057 / 1000000000) (461917 / 125000) (461939 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41567 / 512000) (41571 / 512000) (461917 / 125000) (461939 / 125000) (4056 / 125) (4057 / 125)
    (49419 / 1000) (49519 / 1000) (-69097 / 125) (397591 / 1000000) (596827 / 200) (980817 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (461917 / 125000) (65251725159 / 1000000) (980817 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461917 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461917 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell358 :
    ∀ t ∈ Set.Icc ((41571 / 512000) : ℝ) (1663 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((73519691 / 62500000) : ℝ) ≤ Real.exp (2 * (41571 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41571 / 512000)) (73519691 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1663 / 20480) : ℝ)) ≤ (1176333437 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1663 / 20480)) (1176333437 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65262884153 / 1000000) : ℝ) ≤ Real.exp (3 * (3695393 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3695393 / 1000000)) (65262884153 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41571 / 512000) : ℝ) (1663 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3695393 / 1000000) (369557 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41571 / 512000) (1663 / 20480) (73519691 / 62500000) (1176333437 / 1000000000) (3695393 / 1000000) (369557 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41571 / 512000) (1663 / 20480) (3695393 / 1000000) (369557 / 100000) (649 / 20) (32457 / 1000)
    (1977 / 40) (24763 / 500) (-552781 / 1000) (397541 / 1000000) (2984323 / 1000) (1961299 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3695393 / 1000000) (65262884153 / 1000000) (1961299 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3695393 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3695393 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell359 :
    ∀ t ∈ Set.Icc ((1663 / 20480) : ℝ) (41579 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((294083359 / 250000000) : ℝ) ≤ Real.exp (2 * (1663 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1663 / 20480)) (294083359 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41579 / 512000) : ℝ)) ≤ (1176351817 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41579 / 512000)) (1176351817 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32637120439 / 500000) : ℝ) ≤ Real.exp (3 * (3695451 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3695451 / 1000000)) (32637120439 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1663 / 20480) : ℝ) (41579 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3695451 / 1000000) (3695627 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1663 / 20480) (41579 / 512000) (294083359 / 250000000) (1176351817 / 1000000000) (3695451 / 1000000) (3695627 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1663 / 20480) (41579 / 512000) (3695451 / 1000000) (3695627 / 1000000) (32451 / 1000) (16229 / 500)
    (49433 / 1000) (49533 / 1000) (-138199 / 250) (397491 / 1000000) (2984507 / 1000) (784383 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3695451 / 1000000) (32637120439 / 500000) (784383 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3695451 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3695451 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch017 :
    ∀ t ∈ Set.Icc ((41499 / 512000) : ℝ) (41579 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell340
      hpThetaDensityLowerExpCompact_cell341)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell342
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell343
      hpThetaDensityLowerExpCompact_cell344)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell345
      hpThetaDensityLowerExpCompact_cell346)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell347
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell348
      hpThetaDensityLowerExpCompact_cell349))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell350
      hpThetaDensityLowerExpCompact_cell351)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell352
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell353
      hpThetaDensityLowerExpCompact_cell354)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell355
      hpThetaDensityLowerExpCompact_cell356)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell357
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell358
      hpThetaDensityLowerExpCompact_cell359)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch017
end HodgeProofHP
