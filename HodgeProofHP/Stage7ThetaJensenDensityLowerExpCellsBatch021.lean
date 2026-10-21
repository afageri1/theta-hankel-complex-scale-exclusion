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
theorem hpThetaDensityLowerExpCompact_cell420 :
    ∀ t ∈ Set.Icc ((41819 / 512000) : ℝ) (41823 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1177455163 / 1000000000) : ℝ) ≤ Real.exp (2 * (41819 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41819 / 512000)) (1177455163 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41823 / 512000) : ℝ)) ≤ (588736781 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41823 / 512000)) (588736781 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((206149939 / 3125) : ℝ) ≤ Real.exp (3 * (147959 / 40000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (147959 / 40000)) (206149939 / 3125) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41819 / 512000) : ℝ) (41823 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (147959 / 40000) (3699151 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41819 / 512000) (41823 / 512000) (1177455163 / 1000000000) (588736781 / 500000000) (147959 / 40000) (3699151 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41819 / 512000) (41823 / 512000) (147959 / 40000) (3699151 / 1000000) (16267 / 500) (16271 / 500)
    (2493 / 50) (1249 / 25) (-276707 / 500) (394437 / 1000000) (2995907 / 1000) (3880671 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (147959 / 40000) (206149939 / 3125) (3880671 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (147959 / 40000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (147959 / 40000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell421 :
    ∀ t ∈ Set.Icc ((41823 / 512000) : ℝ) (41827 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1177473561 / 1000000000) : ℝ) ≤ Real.exp (2 * (41823 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41823 / 512000)) (1177473561 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41827 / 512000) : ℝ)) ≤ (29437299 / 25000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41827 / 512000)) (29437299 / 25000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32989729951 / 500000) : ℝ) ≤ Real.exp (3 * (3699033 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3699033 / 1000000)) (32989729951 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41823 / 512000) : ℝ) (41827 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3699033 / 1000000) (3699209 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41823 / 512000) (41827 / 512000) (1177473561 / 1000000000) (29437299 / 25000000) (3699033 / 1000000) (3699209 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41823 / 512000) (41827 / 512000) (3699033 / 1000000) (3699209 / 1000000) (4067 / 125) (32543 / 1000)
    (49867 / 1000) (49967 / 1000) (-69178 / 125) (394387 / 1000000) (599219 / 200) (969999 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3699033 / 1000000) (32989729951 / 500000) (969999 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3699033 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3699033 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell422 :
    ∀ t ∈ Set.Icc ((41827 / 512000) : ℝ) (41831 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1177491959 / 1000000000) : ℝ) ≤ Real.exp (2 * (41827 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41827 / 512000)) (1177491959 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41831 / 512000) : ℝ)) ≤ (1177510359 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41831 / 512000)) (1177510359 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65990743349 / 1000000) : ℝ) ≤ Real.exp (3 * (369909 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (369909 / 100000)) (65990743349 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41827 / 512000) : ℝ) (41831 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (369909 / 100000) (3699267 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41827 / 512000) (41831 / 512000) (1177491959 / 1000000000) (1177510359 / 1000000000) (369909 / 100000) (3699267 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41827 / 512000) (41831 / 512000) (369909 / 100000) (3699267 / 1000000) (32537 / 1000) (4068 / 125)
    (24937 / 500) (1999 / 40) (-553429 / 1000) (197169 / 500000) (2996283 / 1000) (969833 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (369909 / 100000) (65990743349 / 1000000) (969833 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (369909 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (369909 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell423 :
    ∀ t ∈ Set.Icc ((41831 / 512000) : ℝ) (8367 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((588755179 / 500000000) : ℝ) ≤ Real.exp (2 * (41831 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41831 / 512000)) (588755179 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8367 / 102400) : ℝ)) ≤ (588764379 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8367 / 102400)) (588764379 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16500556683 / 250000) : ℝ) ≤ Real.exp (3 * (924787 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (924787 / 250000)) (16500556683 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41831 / 512000) : ℝ) (8367 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (924787 / 250000) (147973 / 40000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41831 / 512000) (8367 / 102400) (588755179 / 500000000) (588764379 / 500000000) (924787 / 250000) (147973 / 40000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41831 / 512000) (8367 / 102400) (924787 / 250000) (147973 / 40000) (16269 / 500) (16273 / 500)
    (49881 / 1000) (24991 / 500) (-553439 / 1000) (24643 / 62500) (299647 / 100) (1939329 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (924787 / 250000) (16500556683 / 250000) (1939329 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (924787 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (924787 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell424 :
    ∀ t ∈ Set.Icc ((8367 / 102400) : ℝ) (41839 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1177528757 / 1000000000) : ℝ) ≤ Real.exp (2 * (8367 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8367 / 102400)) (1177528757 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41839 / 512000) : ℝ)) ≤ (1177547157 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41839 / 512000)) (1177547157 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66013712113 / 1000000) : ℝ) ≤ Real.exp (3 * (1849603 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1849603 / 500000)) (66013712113 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8367 / 102400) : ℝ) (41839 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1849603 / 500000) (3699383 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8367 / 102400) (41839 / 512000) (1177528757 / 1000000000) (1177547157 / 1000000000) (1849603 / 500000) (3699383 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8367 / 102400) (41839 / 512000) (1849603 / 500000) (3699383 / 1000000) (1627 / 50) (32547 / 1000)
    (6236 / 125) (49989 / 1000) (-11069 / 20) (197119 / 500000) (1498329 / 500) (3877983 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1849603 / 500000) (66013712113 / 1000000) (3877983 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1849603 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1849603 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell425 :
    ∀ t ∈ Set.Icc ((41839 / 512000) : ℝ) (41843 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((294386789 / 250000000) : ℝ) ≤ Real.exp (2 * (41839 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41839 / 512000)) (294386789 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41843 / 512000) : ℝ)) ≤ (294391389 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41843 / 512000)) (294391389 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66025199493 / 1000000) : ℝ) ≤ Real.exp (3 * (57801 / 15625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (57801 / 15625)) (66025199493 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41839 / 512000) : ℝ) (41843 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (57801 / 15625) (46243 / 12500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41839 / 512000) (41843 / 512000) (294386789 / 250000000) (294391389 / 250000000) (57801 / 15625) (46243 / 12500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41839 / 512000) (41843 / 512000) (57801 / 15625) (46243 / 12500) (32541 / 1000) (8137 / 250)
    (9979 / 200) (12499 / 250) (-69183 / 125) (394187 / 1000000) (2996843 / 1000) (969327 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (57801 / 15625) (66025199493 / 1000000) (969327 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (57801 / 15625)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (57801 / 15625)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell426 :
    ∀ t ∈ Set.Icc ((41843 / 512000) : ℝ) (41847 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235513111 / 200000000) : ℝ) ≤ Real.exp (2 * (41843 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41843 / 512000)) (235513111 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41847 / 512000) : ℝ)) ≤ (294395989 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41847 / 512000)) (294395989 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8254586109 / 125000) : ℝ) ≤ Real.exp (3 * (1849661 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1849661 / 500000)) (8254586109 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41843 / 512000) : ℝ) (41847 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1849661 / 500000) (1849749 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41843 / 512000) (41847 / 512000) (235513111 / 200000000) (294395989 / 250000000) (1849661 / 500000) (1849749 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41843 / 512000) (41847 / 512000) (1849661 / 500000) (1849749 / 500000) (16271 / 500) (651 / 20)
    (24951 / 500) (50003 / 1000) (-276737 / 500) (394137 / 1000000) (2997031 / 1000) (3876633 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1849661 / 500000) (8254586109 / 125000) (3876633 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1849661 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1849661 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell427 :
    ∀ t ∈ Set.Icc ((41847 / 512000) : ℝ) (41851 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235516791 / 200000000) : ℝ) ≤ Real.exp (2 * (41847 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41847 / 512000)) (235516791 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41851 / 512000) : ℝ)) ≤ (235520471 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41851 / 512000)) (235520471 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((33023991053 / 500000) : ℝ) ≤ Real.exp (3 * (3699379 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3699379 / 1000000)) (33023991053 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41847 / 512000) : ℝ) (41851 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3699379 / 1000000) (924889 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41847 / 512000) (41851 / 512000) (235516791 / 200000000) (235520471 / 200000000) (3699379 / 1000000) (924889 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41847 / 512000) (41851 / 512000) (3699379 / 1000000) (924889 / 250000) (4068 / 125) (32551 / 1000)
    (49909 / 1000) (5001 / 100) (-13837 / 25) (49261 / 125000) (2997219 / 1000) (3875971 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3699379 / 1000000) (33023991053 / 500000) (3875971 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3699379 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3699379 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell428 :
    ∀ t ∈ Set.Icc ((41851 / 512000) : ℝ) (8371 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((588801177 / 500000000) : ℝ) ≤ Real.exp (2 * (41851 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41851 / 512000)) (588801177 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8371 / 102400) : ℝ)) ≤ (294405189 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8371 / 102400)) (294405189 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66059475449 / 1000000) : ℝ) ≤ Real.exp (3 * (3699437 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3699437 / 1000000)) (66059475449 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41851 / 512000) : ℝ) (8371 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3699437 / 1000000) (1849807 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41851 / 512000) (8371 / 102400) (588801177 / 500000000) (294405189 / 250000000) (3699437 / 1000000) (1849807 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41851 / 512000) (8371 / 102400) (3699437 / 1000000) (1849807 / 500000) (6509 / 200) (4069 / 125)
    (12479 / 250) (50017 / 1000) (-55349 / 100) (197019 / 500000) (2997407 / 1000) (121103 / 31250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3699437 / 1000000) (66059475449 / 1000000) (121103 / 31250000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3699437 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3699437 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell429 :
    ∀ t ∈ Set.Icc ((8371 / 102400) : ℝ) (41859 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235524151 / 200000000) : ℝ) ≤ Real.exp (2 * (8371 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8371 / 102400)) (235524151 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41859 / 512000) : ℝ)) ≤ (294409789 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41859 / 512000)) (294409789 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66070970793 / 1000000) : ℝ) ≤ Real.exp (3 * (739899 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (739899 / 200000)) (66070970793 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8371 / 102400) : ℝ) (41859 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (739899 / 200000) (462459 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8371 / 102400) (41859 / 512000) (235524151 / 200000000) (294409789 / 250000000) (739899 / 200000) (462459 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8371 / 102400) (41859 / 512000) (739899 / 200000) (462459 / 125000) (32547 / 1000) (16277 / 500)
    (49923 / 1000) (6253 / 125) (-1107 / 2) (98497 / 250000) (599519 / 200) (1937311 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (739899 / 200000) (66070970793 / 1000000) (1937311 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (739899 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (739899 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell430 :
    ∀ t ∈ Set.Icc ((41859 / 512000) : ℝ) (41863 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235527831 / 200000000) : ℝ) ≤ Real.exp (2 * (41859 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41859 / 512000)) (235527831 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41863 / 512000) : ℝ)) ≤ (1177657557 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41863 / 512000)) (1177657557 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66082468137 / 1000000) : ℝ) ≤ Real.exp (3 * (3699553 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3699553 / 1000000)) (66082468137 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41859 / 512000) : ℝ) (41863 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3699553 / 1000000) (3699729 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41859 / 512000) (41863 / 512000) (235527831 / 200000000) (1177657557 / 1000000000) (3699553 / 1000000) (3699729 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41859 / 512000) (41863 / 512000) (3699553 / 1000000) (3699729 / 1000000) (8137 / 250) (6511 / 200)
    (4993 / 100) (50031 / 1000) (-110703 / 200) (196969 / 500000) (149889 / 50) (968487 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3699553 / 1000000) (66082468137 / 1000000) (968487 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3699553 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3699553 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell431 :
    ∀ t ∈ Set.Icc ((41863 / 512000) : ℝ) (41867 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((294414389 / 250000000) : ℝ) ≤ Real.exp (2 * (41863 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41863 / 512000)) (294414389 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41867 / 512000) : ℝ)) ≤ (588837979 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41867 / 512000)) (588837979 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66093967481 / 1000000) : ℝ) ≤ Real.exp (3 * (3699611 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3699611 / 1000000)) (66093967481 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41863 / 512000) : ℝ) (41867 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3699611 / 1000000) (3699787 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41863 / 512000) (41867 / 512000) (294414389 / 250000000) (588837979 / 500000000) (3699611 / 1000000) (3699787 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41863 / 512000) (41867 / 512000) (3699611 / 1000000) (3699787 / 1000000) (32549 / 1000) (32557 / 1000)
    (49937 / 1000) (25019 / 500) (-22141 / 40) (12309 / 31250) (374746 / 125) (1936637 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3699611 / 1000000) (66093967481 / 1000000) (1936637 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3699611 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3699611 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell432 :
    ∀ t ∈ Set.Icc ((41867 / 512000) : ℝ) (41871 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1177675957 / 1000000000) : ℝ) ≤ Real.exp (2 * (41867 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41867 / 512000)) (1177675957 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41871 / 512000) : ℝ)) ≤ (1177694359 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41871 / 512000)) (1177694359 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66105468827 / 1000000) : ℝ) ≤ Real.exp (3 * (3699669 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3699669 / 1000000)) (66105468827 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41867 / 512000) : ℝ) (41871 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3699669 / 1000000) (739969 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41867 / 512000) (41871 / 512000) (1177675957 / 1000000000) (1177694359 / 1000000000) (3699669 / 1000000) (739969 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41867 / 512000) (41871 / 512000) (3699669 / 1000000) (739969 / 200000) (32551 / 1000) (16279 / 500)
    (6243 / 125) (10009 / 200) (-110707 / 200) (196919 / 500000) (749539 / 250) (19363 / 5000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3699669 / 1000000) (66105468827 / 1000000) (19363 / 5000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3699669 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3699669 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell433 :
    ∀ t ∈ Set.Icc ((41871 / 512000) : ℝ) (335 / 4096), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((588847179 / 500000000) : ℝ) ≤ Real.exp (2 * (41871 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41871 / 512000)) (588847179 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((335 / 4096) : ℝ)) ≤ (1177712761 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (335 / 4096)) (1177712761 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66116773823 / 1000000) : ℝ) ≤ Real.exp (3 * (1849863 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1849863 / 500000)) (66116773823 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41871 / 512000) : ℝ) (335 / 4096),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1849863 / 500000) (3699903 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41871 / 512000) (335 / 4096) (588847179 / 500000000) (1177712761 / 1000000000) (1849863 / 500000) (3699903 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41871 / 512000) (335 / 4096) (1849863 / 500000) (3699903 / 1000000) (4069 / 125) (32559 / 1000)
    (49951 / 1000) (12513 / 250) (-27677 / 50) (393789 / 1000000) (374793 / 125) (1935969 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1849863 / 500000) (66116773823 / 1000000) (1935969 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1849863 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1849863 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell434 :
    ∀ t ∈ Set.Icc ((335 / 4096) : ℝ) (41879 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((29442819 / 25000000) : ℝ) ≤ Real.exp (2 * (335 / 4096)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (335 / 4096)) (29442819 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41879 / 512000) : ℝ)) ≤ (1177731163 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41879 / 512000)) (1177731163 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66128279137 / 1000000) : ℝ) ≤ Real.exp (3 * (462473 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (462473 / 125000)) (66128279137 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((335 / 4096) : ℝ) (41879 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (462473 / 125000) (3699961 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (335 / 4096) (41879 / 512000) (29442819 / 25000000) (1177731163 / 1000000000) (462473 / 125000) (3699961 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (335 / 4096) (41879 / 512000) (462473 / 125000) (3699961 / 1000000) (32553 / 1000) (32561 / 1000)
    (24979 / 500) (50059 / 1000) (-11071 / 20) (393739 / 1000000) (749633 / 250) (120977 / 31250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (462473 / 125000) (66128279137 / 1000000) (120977 / 31250000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (462473 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (462473 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell435 :
    ∀ t ∈ Set.Icc ((41879 / 512000) : ℝ) (41883 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((588865581 / 500000000) : ℝ) ≤ Real.exp (2 * (41879 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41879 / 512000)) (588865581 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41883 / 512000) : ℝ)) ≤ (235549913 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41883 / 512000)) (235549913 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((33069893227 / 500000) : ℝ) ≤ Real.exp (3 * (1849921 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1849921 / 500000)) (33069893227 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41879 / 512000) : ℝ) (41883 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1849921 / 500000) (3700019 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41879 / 512000) (41883 / 512000) (588865581 / 500000000) (235549913 / 200000000) (1849921 / 500000) (3700019 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41879 / 512000) (41883 / 512000) (1849921 / 500000) (3700019 / 1000000) (6511 / 200) (16281 / 500)
    (9993 / 200) (25033 / 500) (-13839 / 25) (393689 / 1000000) (74968 / 25) (3870591 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1849921 / 500000) (33069893227 / 500000) (3870591 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1849921 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1849921 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell436 :
    ∀ t ∈ Set.Icc ((41883 / 512000) : ℝ) (41887 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((294437391 / 250000000) : ℝ) ≤ Real.exp (2 * (41883 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41883 / 512000)) (294437391 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41887 / 512000) : ℝ)) ≤ (1177767967 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41887 / 512000)) (1177767967 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16537823943 / 250000) : ℝ) ≤ Real.exp (3 * (36999 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (36999 / 10000)) (16537823943 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41883 / 512000) : ℝ) (41887 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (36999 / 10000) (925019 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41883 / 512000) (41887 / 512000) (294437391 / 250000000) (1177767967 / 1000000000) (36999 / 10000) (925019 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41883 / 512000) (41887 / 512000) (36999 / 10000) (925019 / 250000) (8139 / 250) (32563 / 1000)
    (12493 / 250) (50073 / 1000) (-22143 / 40) (393639 / 1000000) (374863 / 125) (3869917 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (36999 / 10000) (16537823943 / 250000) (3869917 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (36999 / 10000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (36999 / 10000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell437 :
    ∀ t ∈ Set.Icc ((41887 / 512000) : ℝ) (41891 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((588883983 / 500000000) : ℝ) ≤ Real.exp (2 * (41887 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41887 / 512000)) (588883983 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41891 / 512000) : ℝ)) ≤ (117778637 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41891 / 512000)) (117778637 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((33081403547 / 500000) : ℝ) ≤ Real.exp (3 * (1849979 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1849979 / 500000)) (33081403547 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41887 / 512000) : ℝ) (41891 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1849979 / 500000) (1850067 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41887 / 512000) (41891 / 512000) (588883983 / 500000000) (117778637 / 100000000) (1849979 / 500000) (1850067 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41887 / 512000) (41891 / 512000) (1849979 / 500000) (1850067 / 500000) (32557 / 1000) (6513 / 200)
    (49979 / 1000) (1252 / 25) (-110717 / 200) (393589 / 1000000) (2999093 / 1000) (967311 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1849979 / 500000) (33081403547 / 500000) (967311 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1849979 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1849979 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell438 :
    ∀ t ∈ Set.Icc ((41891 / 512000) : ℝ) (8379 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1177786369 / 1000000000) : ℝ) ≤ Real.exp (2 * (41891 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41891 / 512000)) (1177786369 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8379 / 102400) : ℝ)) ≤ (1177804773 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8379 / 102400)) (1177804773 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8271765237 / 125000) : ℝ) ≤ Real.exp (3 * (740003 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (740003 / 200000)) (8271765237 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41891 / 512000) : ℝ) (8379 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (740003 / 200000) (115631 / 31250) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41891 / 512000) (8379 / 102400) (1177786369 / 1000000000) (1177804773 / 1000000000) (740003 / 200000) (115631 / 31250) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41891 / 512000) (8379 / 102400) (740003 / 200000) (115631 / 31250) (32559 / 1000) (16283 / 500)
    (24993 / 500) (50087 / 1000) (-553591 / 1000) (19677 / 50000) (2999281 / 1000) (1934291 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (740003 / 200000) (8271765237 / 125000) (1934291 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (740003 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (740003 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell439 :
    ∀ t ∈ Set.Icc ((8379 / 102400) : ℝ) (41899 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((294451193 / 250000000) : ℝ) ≤ Real.exp (2 * (8379 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8379 / 102400)) (294451193 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41899 / 512000) : ℝ)) ≤ (1177823177 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41899 / 512000)) (1177823177 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6618563719 / 100000) : ℝ) ≤ Real.exp (3 * (3700073 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3700073 / 1000000)) (6618563719 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8379 / 102400) : ℝ) (41899 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3700073 / 1000000) (14801 / 4000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8379 / 102400) (41899 / 512000) (294451193 / 250000000) (1177823177 / 1000000000) (3700073 / 1000000) (14801 / 4000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8379 / 102400) (41899 / 512000) (3700073 / 1000000) (14801 / 4000) (814 / 25) (32567 / 1000)
    (49993 / 1000) (25047 / 500) (-553601 / 1000) (39349 / 100000) (2999469 / 1000) (3867909 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3700073 / 1000000) (6618563719 / 100000) (3867909 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3700073 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3700073 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch021 :
    ∀ t ∈ Set.Icc ((41819 / 512000) : ℝ) (41899 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell420
      hpThetaDensityLowerExpCompact_cell421)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell422
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell423
      hpThetaDensityLowerExpCompact_cell424)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell425
      hpThetaDensityLowerExpCompact_cell426)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell427
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell428
      hpThetaDensityLowerExpCompact_cell429))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell430
      hpThetaDensityLowerExpCompact_cell431)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell432
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell433
      hpThetaDensityLowerExpCompact_cell434)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell435
      hpThetaDensityLowerExpCompact_cell436)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell437
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell438
      hpThetaDensityLowerExpCompact_cell439)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch021
end HodgeProofHP
