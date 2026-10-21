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
theorem hpThetaDensityLowerExpCompact_cell900 :
    ∀ t ∈ Set.Icc ((47507 / 512000) : ℝ) (47539 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1203909549 / 1000000000) : ℝ) ≤ Real.exp (2 * (47507 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47507 / 512000)) (1203909549 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((47539 / 512000) : ℝ)) ≤ (75253753 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47539 / 512000)) (75253753 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((84646802481 / 1000000) : ℝ) ≤ Real.exp (3 * (3782081 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3782081 / 1000000)) (84646802481 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((47507 / 512000) : ℝ) (47539 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3782081 / 1000000) (945669 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (47507 / 512000) (47539 / 512000) (1203909549 / 1000000000) (75253753 / 62500000) (3782081 / 1000000) (945669 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (47507 / 512000) (47539 / 512000) (3782081 / 1000000) (945669 / 250000) (863 / 25) (34543 / 1000)
    (60267 / 1000) (7577 / 125) (-282121 / 500) (164347 / 500000) (1637897 / 500) (756083 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3782081 / 1000000) (84646802481 / 1000000) (756083 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3782081 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3782081 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell901 :
    ∀ t ∈ Set.Icc ((47539 / 512000) : ℝ) (47571 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1204060047 / 1000000000) : ℝ) ≤ Real.exp (2 * (47539 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47539 / 512000)) (1204060047 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((47571 / 512000) : ℝ)) ≤ (240842113 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47571 / 512000)) (240842113 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((21191750367 / 250000) : ℝ) ≤ Real.exp (3 * (1891277 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1891277 / 500000)) (21191750367 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((47539 / 512000) : ℝ) (47571 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1891277 / 500000) (945787 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (47539 / 512000) (47571 / 512000) (1204060047 / 1000000000) (240842113 / 200000000) (1891277 / 500000) (945787 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (47539 / 512000) (47571 / 512000) (1891277 / 500000) (945787 / 250000) (34531 / 1000) (17277 / 500)
    (60329 / 1000) (30339 / 500) (-564309 / 1000) (6567 / 20000) (327743 / 100) (755011 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1891277 / 500000) (21191750367 / 250000) (755011 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1891277 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1891277 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell902 :
    ∀ t ∈ Set.Icc ((47571 / 512000) : ℝ) (47603 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((301052641 / 250000000) : ℝ) ≤ Real.exp (2 * (47571 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47571 / 512000)) (301052641 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((47603 / 512000) : ℝ)) ≤ (12043611 / 10000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47603 / 512000)) (12043611 / 10000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((84887371139 / 1000000) : ℝ) ≤ Real.exp (3 * (3783027 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3783027 / 1000000)) (84887371139 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((47571 / 512000) : ℝ) (47603 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3783027 / 1000000) (3783621 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (47571 / 512000) (47603 / 512000) (301052641 / 250000000) (12043611 / 10000000) (3783027 / 1000000) (3783621 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (47571 / 512000) (47603 / 512000) (3783027 / 1000000) (3783621 / 1000000) (34543 / 1000) (6913 / 200)
    (60391 / 1000) (3037 / 50) (-56437 / 100) (41001 / 125000) (3279069 / 1000) (3015761 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3783027 / 1000000) (84887371139 / 1000000) (3015761 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3783027 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3783027 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell903 :
    ∀ t ∈ Set.Icc ((47603 / 512000) : ℝ) (9527 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1204361099 / 1000000000) : ℝ) ≤ Real.exp (2 * (47603 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47603 / 512000)) (1204361099 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9527 / 102400) : ℝ)) ≤ (240902331 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9527 / 102400)) (240902331 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((42503955867 / 500000) : ℝ) ≤ Real.exp (3 * (7567 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (7567 / 2000)) (42503955867 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((47603 / 512000) : ℝ) (9527 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (7567 / 2000) (1892047 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (47603 / 512000) (9527 / 102400) (1204361099 / 1000000000) (240902331 / 200000000) (7567 / 2000) (1892047 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (47603 / 512000) (9527 / 102400) (7567 / 2000) (1892047 / 500000) (17277 / 500) (34577 / 1000)
    (30227 / 500) (30401 / 500) (-70554 / 125) (163833 / 500000) (3280709 / 1000) (602297 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (7567 / 2000) (42503955867 / 500000) (602297 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7567 / 2000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7567 / 2000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell904 :
    ∀ t ∈ Set.Icc ((9527 / 102400) : ℝ) (47667 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((602255827 / 500000000) : ℝ) ≤ Real.exp (2 * (9527 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9527 / 102400)) (602255827 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((47667 / 512000) : ℝ)) ≤ (301165557 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47667 / 512000)) (301165557 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((42564311749 / 500000) : ℝ) ≤ Real.exp (3 * (3783973 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3783973 / 1000000)) (42564311749 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9527 / 102400) : ℝ) (47667 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3783973 / 1000000) (3784567 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9527 / 102400) (47667 / 512000) (602255827 / 500000000) (301165557 / 250000000) (3783973 / 1000000) (3784567 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9527 / 102400) (47667 / 512000) (3783973 / 1000000) (3784567 / 1000000) (17283 / 500) (8647 / 250)
    (15129 / 250) (12173 / 200) (-282247 / 500) (81831 / 250000) (65647 / 20) (601443 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3783973 / 1000000) (42564311749 / 500000) (601443 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3783973 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3783973 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell905 :
    ∀ t ∈ Set.Icc ((47667 / 512000) : ℝ) (47699 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1204662227 / 1000000000) : ℝ) ≤ Real.exp (2 * (47667 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47667 / 512000)) (1204662227 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((47699 / 512000) : ℝ)) ≤ (60240641 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47699 / 512000)) (60240641 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((85249506673 / 1000000) : ℝ) ≤ Real.exp (3 * (1892223 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1892223 / 500000)) (85249506673 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((47667 / 512000) : ℝ) (47699 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1892223 / 500000) (47313 / 12500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (47667 / 512000) (47699 / 512000) (1204662227 / 1000000000) (60240641 / 50000000) (1892223 / 500000) (47313 / 12500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (47667 / 512000) (47699 / 512000) (1892223 / 500000) (47313 / 12500) (34577 / 1000) (173 / 5)
    (30289 / 500) (60927 / 1000) (-141139 / 250) (163491 / 500000) (3283991 / 1000) (60059 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1892223 / 500000) (85249506673 / 1000000) (60059 / 20000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1892223 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1892223 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell906 :
    ∀ t ∈ Set.Icc ((47699 / 512000) : ℝ) (47731 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1204812819 / 1000000000) : ℝ) ≤ Real.exp (2 * (47699 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47699 / 512000)) (1204812819 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((47731 / 512000) : ℝ)) ≤ (1204963431 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47731 / 512000)) (1204963431 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((42685280751 / 500000) : ℝ) ≤ Real.exp (3 * (3784919 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3784919 / 1000000)) (42685280751 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((47699 / 512000) : ℝ) (47731 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3784919 / 1000000) (1892757 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (47699 / 512000) (47731 / 512000) (1204812819 / 1000000000) (1204963431 / 1000000000) (3784919 / 1000000) (1892757 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (47699 / 512000) (47731 / 512000) (3784919 / 1000000) (1892757 / 500000) (34589 / 1000) (34611 / 1000)
    (1516 / 25) (6099 / 100) (-141153 / 250) (326641 / 1000000) (821409 / 250) (749673 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3784919 / 1000000) (42685280751 / 500000) (749673 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3784919 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3784919 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell907 :
    ∀ t ∈ Set.Icc ((47731 / 512000) : ℝ) (47763 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((120496343 / 100000000) : ℝ) ≤ Real.exp (2 * (47731 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47731 / 512000)) (120496343 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((47763 / 512000) : ℝ)) ≤ (1205114061 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47763 / 512000)) (1205114061 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8549178823 / 100000) : ℝ) ≤ Real.exp (3 * (236587 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (236587 / 62500)) (8549178823 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((47731 / 512000) : ℝ) (47763 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (236587 / 62500) (3785987 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (47731 / 512000) (47763 / 512000) (120496343 / 100000000) (1205114061 / 1000000000) (236587 / 62500) (3785987 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (47731 / 512000) (47763 / 512000) (236587 / 62500) (3785987 / 1000000) (173 / 5) (34623 / 1000)
    (30351 / 500) (15263 / 250) (-282337 / 500) (3263 / 10000) (3287279 / 1000) (74861 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (236587 / 62500) (8549178823 / 100000) (74861 / 25000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (236587 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (236587 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell908 :
    ∀ t ∈ Set.Icc ((47763 / 512000) : ℝ) (9559 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((60255703 / 50000000) : ℝ) ≤ Real.exp (2 * (47763 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47763 / 512000)) (60255703 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9559 / 102400) : ℝ)) ≤ (120526471 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9559 / 102400)) (120526471 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((85613187101 / 1000000) : ℝ) ≤ Real.exp (3 * (757173 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (757173 / 200000)) (85613187101 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((47763 / 512000) : ℝ) (9559 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (757173 / 200000) (189323 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (47763 / 512000) (9559 / 102400) (60255703 / 50000000) (120526471 / 100000000) (757173 / 200000) (189323 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (47763 / 512000) (9559 / 102400) (757173 / 200000) (189323 / 50000) (8653 / 250) (17317 / 500)
    (12153 / 200) (30557 / 500) (-112947 / 200) (8149 / 25000) (1644461 / 500) (1495097 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (757173 / 200000) (85613187101 / 1000000) (1495097 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (757173 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (757173 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell909 :
    ∀ t ∈ Set.Icc ((9559 / 102400) : ℝ) (47827 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1205264709 / 1000000000) : ℝ) ≤ Real.exp (2 * (9559 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9559 / 102400)) (1205264709 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((47827 / 512000) : ℝ)) ≤ (602707689 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47827 / 512000)) (602707689 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((85735015563 / 1000000) : ℝ) ≤ Real.exp (3 * (3786339 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3786339 / 1000000)) (85735015563 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9559 / 102400) : ℝ) (47827 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3786339 / 1000000) (3786933 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9559 / 102400) (47827 / 512000) (1205264709 / 1000000000) (602707689 / 500000000) (3786339 / 1000000) (3786933 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9559 / 102400) (47827 / 512000) (3786339 / 1000000) (3786933 / 1000000) (34623 / 1000) (17323 / 500)
    (60827 / 1000) (61177 / 1000) (-564801 / 1000) (162809 / 500000) (658113 / 200) (597189 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3786339 / 1000000) (85735015563 / 1000000) (597189 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3786339 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3786339 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell910 :
    ∀ t ∈ Set.Icc ((47827 / 512000) : ℝ) (47859 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1205415377 / 1000000000) : ℝ) ≤ Real.exp (2 * (47827 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47827 / 512000)) (1205415377 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((47859 / 512000) : ℝ)) ≤ (75347879 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47859 / 512000)) (75347879 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((85856759817 / 1000000) : ℝ) ≤ Real.exp (3 * (946703 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (946703 / 250000)) (85856759817 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((47827 / 512000) : ℝ) (47859 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (946703 / 250000) (3787407 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (47827 / 512000) (47859 / 512000) (1205415377 / 1000000000) (75347879 / 62500000) (946703 / 250000) (3787407 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (47827 / 512000) (47859 / 512000) (946703 / 250000) (3787407 / 1000000) (6927 / 200) (34657 / 1000)
    (6089 / 100) (61239 / 1000) (-564857 / 1000) (325279 / 1000000) (3292213 / 1000) (2981711 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (946703 / 250000) (85856759817 / 1000000) (2981711 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (946703 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (946703 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell911 :
    ∀ t ∈ Set.Icc ((47859 / 512000) : ℝ) (47891 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1205566063 / 1000000000) : ℝ) ≤ Real.exp (2 * (47859 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47859 / 512000)) (1205566063 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((47891 / 512000) : ℝ)) ≤ (1205716769 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47891 / 512000)) (1205716769 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((85978676949 / 1000000) : ℝ) ≤ Real.exp (3 * (757457 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (757457 / 200000)) (85978676949 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((47859 / 512000) : ℝ) (47891 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (757457 / 200000) (94697 / 25000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (47859 / 512000) (47891 / 512000) (1205566063 / 1000000000) (1205716769 / 1000000000) (757457 / 200000) (94697 / 25000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (47859 / 512000) (47891 / 512000) (757457 / 200000) (94697 / 25000) (17323 / 500) (34669 / 1000)
    (7619 / 125) (30651 / 500) (-282459 / 500) (324939 / 1000000) (1646929 / 500) (2977483 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (757457 / 200000) (85978676949 / 1000000) (2977483 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (757457 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (757457 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell912 :
    ∀ t ∈ Set.Icc ((47891 / 512000) : ℝ) (47923 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((37678649 / 31250000) : ℝ) ≤ Real.exp (2 * (47891 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47891 / 512000)) (37678649 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((47923 / 512000) : ℝ)) ≤ (1205867493 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47923 / 512000)) (1205867493 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((43050512753 / 500000) : ℝ) ≤ Real.exp (3 * (3787759 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3787759 / 1000000)) (43050512753 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((47891 / 512000) : ℝ) (47923 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3787759 / 1000000) (1894177 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (47891 / 512000) (47923 / 512000) (37678649 / 31250000) (1205867493 / 1000000000) (3787759 / 1000000) (1894177 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (47891 / 512000) (47923 / 512000) (3787759 / 1000000) (1894177 / 500000) (17329 / 500) (867 / 25)
    (12203 / 200) (12273 / 200) (-564979 / 1000) (324599 / 1000000) (3295507 / 1000) (743313 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3787759 / 1000000) (43050512753 / 500000) (743313 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3787759 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3787759 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell913 :
    ∀ t ∈ Set.Icc ((47923 / 512000) : ℝ) (9591 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((301466873 / 250000000) : ℝ) ≤ Real.exp (2 * (47923 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47923 / 512000)) (301466873 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9591 / 102400) : ℝ)) ≤ (301504559 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9591 / 102400)) (301504559 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((10777911187 / 125000) : ℝ) ≤ Real.exp (3 * (473529 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (473529 / 125000)) (10777911187 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((47923 / 512000) : ℝ) (9591 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (473529 / 125000) (3788827 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (47923 / 512000) (9591 / 102400) (301466873 / 250000000) (301504559 / 250000000) (473529 / 125000) (3788827 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (47923 / 512000) (9591 / 102400) (473529 / 125000) (3788827 / 1000000) (34669 / 1000) (8673 / 250)
    (61077 / 1000) (61427 / 1000) (-14126 / 25) (324261 / 1000000) (3297153 / 1000) (742259 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (473529 / 125000) (10777911187 / 125000) (742259 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (473529 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (473529 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell914 :
    ∀ t ∈ Set.Icc ((9591 / 102400) : ℝ) (47987 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((241203647 / 200000000) : ℝ) ≤ Real.exp (2 * (9591 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9591 / 102400)) (241203647 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((47987 / 512000) : ℝ)) ≤ (603084499 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47987 / 512000)) (603084499 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((86345986139 / 1000000) : ℝ) ≤ Real.exp (3 * (1894353 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1894353 / 500000)) (86345986139 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9591 / 102400) : ℝ) (47987 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1894353 / 500000) (3789301 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9591 / 102400) (47987 / 512000) (241203647 / 200000000) (603084499 / 500000000) (1894353 / 500000) (3789301 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9591 / 102400) (47987 / 512000) (1894353 / 500000) (3789301 / 1000000) (34681 / 1000) (34703 / 1000)
    (3057 / 50) (6149 / 100) (-565101 / 1000) (323921 / 1000000) (824701 / 250) (2964817 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1894353 / 500000) (86345986139 / 1000000) (2964817 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1894353 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1894353 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell915 :
    ∀ t ∈ Set.Icc ((47987 / 512000) : ℝ) (48019 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1206168997 / 1000000000) : ℝ) ≤ Real.exp (2 * (47987 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47987 / 512000)) (1206168997 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((48019 / 512000) : ℝ)) ≤ (603159889 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (48019 / 512000)) (603159889 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((43234298987 / 500000) : ℝ) ≤ Real.exp (3 * (3789179 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3789179 / 1000000)) (43234298987 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((47987 / 512000) : ℝ) (48019 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3789179 / 1000000) (151591 / 40000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (47987 / 512000) (48019 / 512000) (1206168997 / 1000000000) (603159889 / 500000000) (3789179 / 1000000) (151591 / 40000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (47987 / 512000) (48019 / 512000) (3789179 / 1000000) (151591 / 40000) (8673 / 250) (6943 / 200)
    (30601 / 500) (61553 / 1000) (-141289 / 250) (323583 / 1000000) (660091 / 200) (2960613 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3789179 / 1000000) (43234298987 / 500000) (2960613 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3789179 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3789179 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell916 :
    ∀ t ∈ Set.Icc ((48019 / 512000) : ℝ) (48051 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1206319777 / 1000000000) : ℝ) ≤ Real.exp (2 * (48019 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (48019 / 512000)) (1206319777 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((48051 / 512000) : ℝ)) ≤ (603235289 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (48051 / 512000)) (603235289 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((86591643693 / 1000000) : ℝ) ≤ Real.exp (3 * (3789653 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3789653 / 1000000)) (86591643693 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((48019 / 512000) : ℝ) (48051 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3789653 / 1000000) (473781 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (48019 / 512000) (48051 / 512000) (1206319777 / 1000000000) (603235289 / 500000000) (3789653 / 1000000) (473781 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (48019 / 512000) (48051 / 512000) (3789653 / 1000000) (473781 / 125000) (4338 / 125) (34727 / 1000)
    (12253 / 200) (12323 / 200) (-565221 / 1000) (64649 / 200000) (3302103 / 1000) (1478203 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3789653 / 1000000) (86591643693 / 1000000) (1478203 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3789653 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3789653 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell917 :
    ∀ t ∈ Set.Icc ((48051 / 512000) : ℝ) (48083 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1206470577 / 1000000000) : ℝ) ≤ Real.exp (2 * (48051 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (48051 / 512000)) (1206470577 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((48083 / 512000) : ℝ)) ≤ (301655349 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (48083 / 512000)) (301655349 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((86714864507 / 1000000) : ℝ) ≤ Real.exp (3 * (3790127 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3790127 / 1000000)) (86714864507 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((48051 / 512000) : ℝ) (48083 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3790127 / 1000000) (1895361 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (48051 / 512000) (48083 / 512000) (1206470577 / 1000000000) (301655349 / 250000000) (3790127 / 1000000) (1895361 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (48051 / 512000) (48083 / 512000) (3790127 / 1000000) (1895361 / 500000) (6943 / 200) (17369 / 500)
    (7666 / 125) (30839 / 500) (-282641 / 500) (161453 / 500000) (660751 / 200) (590441 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3790127 / 1000000) (86714864507 / 1000000) (590441 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3790127 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3790127 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell918 :
    ∀ t ∈ Set.Icc ((48083 / 512000) : ℝ) (9623 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((241324279 / 200000000) : ℝ) ≤ Real.exp (2 * (48083 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (48083 / 512000)) (241324279 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9623 / 102400) : ℝ)) ≤ (1206772233 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9623 / 102400)) (1206772233 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((43419130333 / 500000) : ℝ) ≤ Real.exp (3 * (3790601 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3790601 / 1000000)) (43419130333 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((48083 / 512000) : ℝ) (9623 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3790601 / 1000000) (947799 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (48083 / 512000) (9623 / 102400) (241324279 / 200000000) (1206772233 / 1000000000) (3790601 / 1000000) (947799 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (48083 / 512000) (9623 / 102400) (3790601 / 1000000) (947799 / 250000) (34727 / 1000) (139 / 4)
    (6139 / 100) (61741 / 1000) (-282671 / 500) (322569 / 1000000) (3305407 / 1000) (294801 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3790601 / 1000000) (43419130333 / 500000) (294801 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3790601 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3790601 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell919 :
    ∀ t ∈ Set.Icc ((9623 / 102400) : ℝ) (48147 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((150846529 / 125000000) : ℝ) ≤ Real.exp (2 * (9623 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9623 / 102400)) (150846529 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((48147 / 512000) : ℝ)) ≤ (1206923089 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (48147 / 512000)) (1206923089 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((86961571533 / 1000000) : ℝ) ≤ Real.exp (3 * (1895537 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1895537 / 500000)) (86961571533 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9623 / 102400) : ℝ) (48147 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1895537 / 500000) (379167 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9623 / 102400) (48147 / 512000) (150846529 / 125000000) (1206923089 / 1000000000) (1895537 / 500000) (379167 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9623 / 102400) (48147 / 512000) (1895537 / 500000) (379167 / 100000) (17369 / 500) (34761 / 1000)
    (61453 / 1000) (15451 / 250) (-565397 / 1000) (40279 / 125000) (3307061 / 1000) (294383 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1895537 / 500000) (86961571533 / 1000000) (294383 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1895537 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1895537 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch045 :
    ∀ t ∈ Set.Icc ((47507 / 512000) : ℝ) (48147 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell900
      hpThetaDensityLowerExpCompact_cell901)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell902
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell903
      hpThetaDensityLowerExpCompact_cell904)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell905
      hpThetaDensityLowerExpCompact_cell906)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell907
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell908
      hpThetaDensityLowerExpCompact_cell909))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell910
      hpThetaDensityLowerExpCompact_cell911)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell912
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell913
      hpThetaDensityLowerExpCompact_cell914)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell915
      hpThetaDensityLowerExpCompact_cell916)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell917
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell918
      hpThetaDensityLowerExpCompact_cell919)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch045
end HodgeProofHP
