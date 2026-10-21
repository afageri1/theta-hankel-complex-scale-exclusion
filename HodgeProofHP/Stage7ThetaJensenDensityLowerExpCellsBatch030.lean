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
theorem hpThetaDensityLowerExpCompact_cell600 :
    ∀ t ∈ Set.Icc ((42883 / 512000) : ℝ) (42891 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((236471829 / 200000000) : ℝ) ≤ Real.exp (2 * (42883 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42883 / 512000)) (236471829 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42891 / 512000) : ℝ)) ≤ (18474939 / 15625000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42891 / 512000)) (18474939 / 15625000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((17272110599 / 250000) : ℝ) ≤ Real.exp (3 * (3714381 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3714381 / 1000000)) (17272110599 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42883 / 512000) : ℝ) (42891 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3714381 / 1000000) (464327 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42883 / 512000) (42891 / 512000) (236471829 / 200000000) (18474939 / 15625000) (3714381 / 1000000) (464327 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42883 / 512000) (42891 / 512000) (3714381 / 1000000) (464327 / 125000) (16449 / 500) (8227 / 250)
    (51731 / 1000) (25933 / 500) (-27789 / 50) (76273 / 200000) (1523161 / 500) (926349 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3714381 / 1000000) (17272110599 / 250000) (926349 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3714381 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3714381 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell601 :
    ∀ t ∈ Set.Icc ((42891 / 512000) : ℝ) (42899 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((236479219 / 200000000) : ℝ) ≤ Real.exp (2 * (42891 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42891 / 512000)) (236479219 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42899 / 512000) : ℝ)) ≤ (591216523 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42899 / 512000)) (591216523 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((34556244673 / 500000) : ℝ) ≤ Real.exp (3 * (3714497 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3714497 / 1000000)) (34556244673 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42891 / 512000) : ℝ) (42899 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3714497 / 1000000) (928683 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42891 / 512000) (42899 / 512000) (236479219 / 200000000) (591216523 / 500000000) (3714497 / 1000000) (928683 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42891 / 512000) (42899 / 512000) (3714497 / 1000000) (928683 / 250000) (32901 / 1000) (3291 / 100)
    (25873 / 500) (1297 / 25) (-555799 / 1000) (95317 / 250000) (1523351 / 500) (3704107 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3714497 / 1000000) (34556244673 / 500000) (3704107 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3714497 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3714497 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell602 :
    ∀ t ∈ Set.Icc ((42899 / 512000) : ℝ) (42907 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((236486609 / 200000000) : ℝ) ≤ Real.exp (2 * (42899 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42899 / 512000)) (236486609 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42907 / 512000) : ℝ)) ≤ (591234999 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42907 / 512000)) (591234999 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13827308933 / 200000) : ℝ) ≤ Real.exp (3 * (3714613 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3714613 / 1000000)) (13827308933 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42899 / 512000) : ℝ) (42907 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3714613 / 1000000) (116089 / 31250) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42899 / 512000) (42907 / 512000) (236486609 / 200000000) (591234999 / 500000000) (3714613 / 1000000) (116089 / 31250) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42899 / 512000) (42907 / 512000) (3714613 / 1000000) (116089 / 31250) (4113 / 125) (32913 / 1000)
    (1294 / 25) (10379 / 200) (-555819 / 1000) (381171 / 1000000) (3047083 / 1000) (1851409 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3714613 / 1000000) (13827308933 / 200000) (1851409 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3714613 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3714613 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell603 :
    ∀ t ∈ Set.Icc ((42907 / 512000) : ℝ) (8583 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1182469997 / 1000000000) : ℝ) ≤ Real.exp (2 * (42907 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42907 / 512000)) (1182469997 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8583 / 102400) : ℝ)) ≤ (1182506951 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8583 / 102400)) (1182506951 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((69160608357 / 1000000) : ℝ) ≤ Real.exp (3 * (3714729 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3714729 / 1000000)) (69160608357 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42907 / 512000) : ℝ) (8583 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3714729 / 1000000) (928741 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42907 / 512000) (8583 / 102400) (1182469997 / 1000000000) (1182506951 / 1000000000) (3714729 / 1000000) (928741 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42907 / 512000) (8583 / 102400) (3714729 / 1000000) (928741 / 250000) (32907 / 1000) (8229 / 250)
    (25887 / 500) (51909 / 1000) (-277919 / 500) (190537 / 500000) (3047463 / 1000) (370153 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3714729 / 1000000) (69160608357 / 1000000) (370153 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3714729 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3714729 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell604 :
    ∀ t ∈ Set.Icc ((8583 / 102400) : ℝ) (42923 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((23650139 / 20000000) : ℝ) ≤ Real.exp (2 * (8583 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8583 / 102400)) (23650139 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42923 / 512000) : ℝ)) ≤ (36954497 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42923 / 512000)) (36954497 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2767387217 / 40000) : ℝ) ≤ Real.exp (3 * (742969 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (742969 / 200000)) (2767387217 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8583 / 102400) : ℝ) (42923 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (742969 / 200000) (92877 / 25000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8583 / 102400) (42923 / 512000) (23650139 / 20000000) (36954497 / 31250000) (742969 / 200000) (92877 / 25000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8583 / 102400) (42923 / 512000) (742969 / 200000) (92877 / 25000) (32909 / 1000) (32919 / 1000)
    (51789 / 1000) (51923 / 1000) (-555857 / 1000) (380977 / 1000000) (761961 / 250) (1850121 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (742969 / 200000) (2767387217 / 40000) (1850121 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (742969 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (742969 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell605 :
    ∀ t ∈ Set.Icc ((42923 / 512000) : ℝ) (42931 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1182543903 / 1000000000) : ℝ) ≤ Real.exp (2 * (42923 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42923 / 512000)) (1182543903 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42931 / 512000) : ℝ)) ≤ (1182580859 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42931 / 512000)) (1182580859 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8651095109 / 125000) : ℝ) ≤ Real.exp (3 * (3714961 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3714961 / 1000000)) (8651095109 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42923 / 512000) : ℝ) (42931 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3714961 / 1000000) (3715197 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42923 / 512000) (42931 / 512000) (1182543903 / 1000000000) (1182580859 / 1000000000) (3714961 / 1000000) (3715197 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42923 / 512000) (42931 / 512000) (3714961 / 1000000) (3715197 / 1000000) (4114 / 125) (32921 / 1000)
    (51803 / 1000) (25969 / 500) (-69484 / 125) (380881 / 1000000) (762057 / 250) (1849477 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3714961 / 1000000) (8651095109 / 125000) (1849477 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3714961 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3714961 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell606 :
    ∀ t ∈ Set.Icc ((42931 / 512000) : ℝ) (42939 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((591290429 / 500000000) : ℝ) ≤ Real.exp (2 * (42931 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42931 / 512000)) (591290429 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42939 / 512000) : ℝ)) ≤ (147827227 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42939 / 512000)) (147827227 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((69232849699 / 1000000) : ℝ) ≤ Real.exp (3 * (3715077 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3715077 / 1000000)) (69232849699 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42931 / 512000) : ℝ) (42939 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3715077 / 1000000) (3715313 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42931 / 512000) (42939 / 512000) (591290429 / 500000000) (147827227 / 125000000) (3715077 / 1000000) (3715313 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42931 / 512000) (42939 / 512000) (3715077 / 1000000) (3715313 / 1000000) (6583 / 200) (8231 / 250)
    (51817 / 1000) (6494 / 125) (-138973 / 250) (23799 / 62500) (3048609 / 1000) (3697667 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3715077 / 1000000) (69232849699 / 1000000) (3697667 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3715077 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3715077 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell607 :
    ∀ t ∈ Set.Icc ((42939 / 512000) : ℝ) (42947 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((236523563 / 200000000) : ℝ) ≤ Real.exp (2 * (42939 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42939 / 512000)) (236523563 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42947 / 512000) : ℝ)) ≤ (1182654773 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42947 / 512000)) (1182654773 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2164279591 / 31250) : ℝ) ≤ Real.exp (3 * (3715193 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3715193 / 1000000)) (2164279591 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42939 / 512000) : ℝ) (42947 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3715193 / 1000000) (3715429 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42939 / 512000) (42947 / 512000) (236523563 / 200000000) (1182654773 / 1000000000) (3715193 / 1000000) (3715429 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42939 / 512000) (42947 / 512000) (3715193 / 1000000) (3715429 / 1000000) (16459 / 500) (32927 / 1000)
    (51831 / 1000) (51967 / 1000) (-555911 / 1000) (380687 / 1000000) (3048989 / 1000) (3696381 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3715193 / 1000000) (2164279591 / 31250) (3696381 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3715193 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3715193 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell608 :
    ∀ t ∈ Set.Icc ((42947 / 512000) : ℝ) (8591 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((295663693 / 250000000) : ℝ) ≤ Real.exp (2 * (42947 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42947 / 512000)) (295663693 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8591 / 102400) : ℝ)) ≤ (295672933 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8591 / 102400)) (295672933 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((69281052511 / 1000000) : ℝ) ≤ Real.exp (3 * (3715309 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3715309 / 1000000)) (69281052511 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42947 / 512000) : ℝ) (8591 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3715309 / 1000000) (743109 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42947 / 512000) (8591 / 102400) (295663693 / 250000000) (295672933 / 250000000) (3715309 / 1000000) (743109 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42947 / 512000) (8591 / 102400) (3715309 / 1000000) (743109 / 200000) (823 / 25) (3293 / 100)
    (25923 / 500) (51981 / 1000) (-55593 / 100) (38059 / 100000) (304937 / 100) (1847547 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3715309 / 1000000) (69281052511 / 1000000) (1847547 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3715309 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3715309 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell609 :
    ∀ t ∈ Set.Icc ((8591 / 102400) : ℝ) (42963 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1182691731 / 1000000000) : ℝ) ≤ Real.exp (2 * (8591 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8591 / 102400)) (1182691731 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42963 / 512000) : ℝ)) ≤ (1182728691 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42963 / 512000)) (1182728691 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4331585901 / 62500) : ℝ) ≤ Real.exp (3 * (1857713 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1857713 / 500000)) (4331585901 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8591 / 102400) : ℝ) (42963 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1857713 / 500000) (3715661 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8591 / 102400) (42963 / 512000) (1182691731 / 1000000000) (1182728691 / 1000000000) (1857713 / 500000) (3715661 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8591 / 102400) (42963 / 512000) (1857713 / 500000) (3715661 / 1000000) (32923 / 1000) (8233 / 250)
    (2593 / 50) (10399 / 200) (-277977 / 500) (95123 / 250000) (3049751 / 1000) (1846899 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1857713 / 500000) (4331585901 / 62500) (1846899 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1857713 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1857713 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell610 :
    ∀ t ∈ Set.Icc ((42963 / 512000) : ℝ) (42971 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((118272869 / 100000000) : ℝ) ≤ Real.exp (2 * (42963 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42963 / 512000)) (118272869 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42971 / 512000) : ℝ)) ≤ (295691413 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42971 / 512000)) (295691413 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((69329496871 / 1000000) : ℝ) ≤ Real.exp (3 * (1857771 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1857771 / 500000)) (69329496871 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42963 / 512000) : ℝ) (42971 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1857771 / 500000) (3715777 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42963 / 512000) (42971 / 512000) (118272869 / 100000000) (295691413 / 250000000) (1857771 / 500000) (3715777 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42963 / 512000) (42971 / 512000) (1857771 / 500000) (3715777 / 1000000) (16463 / 500) (6587 / 200)
    (415 / 8) (52009 / 1000) (-277987 / 500) (76079 / 200000) (762533 / 250) (3692513 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1857771 / 500000) (69329496871 / 1000000) (3692513 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1857771 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1857771 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell611 :
    ∀ t ∈ Set.Icc ((42971 / 512000) : ℝ) (42979 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1182765651 / 1000000000) : ℝ) ≤ Real.exp (2 * (42971 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42971 / 512000)) (1182765651 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42979 / 512000) : ℝ)) ≤ (591401307 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42979 / 512000)) (591401307 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((69353627723 / 1000000) : ℝ) ≤ Real.exp (3 * (1857829 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1857829 / 500000)) (69353627723 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42971 / 512000) : ℝ) (42979 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1857829 / 500000) (3715893 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42971 / 512000) (42979 / 512000) (1182765651 / 1000000000) (591401307 / 500000000) (1857829 / 500000) (3715893 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42971 / 512000) (42979 / 512000) (1857829 / 500000) (3715893 / 1000000) (32929 / 1000) (16469 / 500)
    (51889 / 1000) (6503 / 125) (-555993 / 1000) (380299 / 1000000) (3050513 / 1000) (922807 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1857829 / 500000) (69353627723 / 1000000) (922807 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1857829 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1857829 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell612 :
    ∀ t ∈ Set.Icc ((42979 / 512000) : ℝ) (42987 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1182802613 / 1000000000) : ℝ) ≤ Real.exp (2 * (42979 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42979 / 512000)) (1182802613 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42987 / 512000) : ℝ)) ≤ (1182839577 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42987 / 512000)) (1182839577 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((69377766973 / 1000000) : ℝ) ≤ Real.exp (3 * (1857887 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1857887 / 500000)) (69377766973 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42979 / 512000) : ℝ) (42987 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1857887 / 500000) (3716009 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42979 / 512000) (42987 / 512000) (1182802613 / 1000000000) (1182839577 / 1000000000) (1857887 / 500000) (3716009 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42979 / 512000) (42987 / 512000) (1857887 / 500000) (3716009 / 1000000) (32931 / 1000) (32941 / 1000)
    (51903 / 1000) (26019 / 500) (-139003 / 250) (190101 / 500000) (1525447 / 500) (3689943 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1857887 / 500000) (69377766973 / 1000000) (3689943 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1857887 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1857887 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell613 :
    ∀ t ∈ Set.Icc ((42987 / 512000) : ℝ) (8599 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((147854947 / 125000000) : ℝ) ≤ Real.exp (2 * (42987 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42987 / 512000)) (147854947 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8599 / 102400) : ℝ)) ≤ (591438271 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8599 / 102400)) (591438271 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((555215317 / 8000) : ℝ) ≤ Real.exp (3 * (371589 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (371589 / 100000)) (555215317 / 8000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42987 / 512000) : ℝ) (8599 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (371589 / 100000) (29729 / 8000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42987 / 512000) (8599 / 102400) (147854947 / 125000000) (591438271 / 500000000) (371589 / 100000) (29729 / 8000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42987 / 512000) (8599 / 102400) (371589 / 100000) (29729 / 8000) (16467 / 500) (4118 / 125)
    (25959 / 500) (13013 / 250) (-556031 / 1000) (76021 / 200000) (122051 / 40) (184433 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (371589 / 100000) (555215317 / 8000) (184433 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (371589 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (371589 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell614 :
    ∀ t ∈ Set.Icc ((8599 / 102400) : ℝ) (43003 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1182876541 / 1000000000) : ℝ) ≤ Real.exp (2 * (8599 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8599 / 102400)) (1182876541 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43003 / 512000) : ℝ)) ≤ (1182913507 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43003 / 512000)) (1182913507 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((34713035341 / 500000) : ℝ) ≤ Real.exp (3 * (1858003 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1858003 / 500000)) (34713035341 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8599 / 102400) : ℝ) (43003 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1858003 / 500000) (1858121 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8599 / 102400) (43003 / 512000) (1182876541 / 1000000000) (1182913507 / 1000000000) (1858003 / 500000) (1858121 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8599 / 102400) (43003 / 512000) (1858003 / 500000) (1858121 / 500000) (32937 / 1000) (16473 / 500)
    (12983 / 250) (52067 / 1000) (-278023 / 500) (380009 / 1000000) (3051659 / 1000) (230461 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1858003 / 500000) (34713035341 / 500000) (230461 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1858003 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1858003 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell615 :
    ∀ t ∈ Set.Icc ((43003 / 512000) : ℝ) (43011 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((591456753 / 500000000) : ℝ) ≤ Real.exp (2 * (43003 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43003 / 512000)) (591456753 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43011 / 512000) : ℝ)) ≤ (591475237 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43011 / 512000)) (591475237 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((34725117573 / 500000) : ℝ) ≤ Real.exp (3 * (1858061 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1858061 / 500000)) (34725117573 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43003 / 512000) : ℝ) (43011 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1858061 / 500000) (1858179 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43003 / 512000) (43011 / 512000) (591456753 / 500000000) (591475237 / 500000000) (1858061 / 500000) (1858179 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43003 / 512000) (43011 / 512000) (1858061 / 500000) (1858179 / 500000) (1647 / 50) (32949 / 1000)
    (25973 / 500) (52081 / 1000) (-111213 / 200) (47489 / 125000) (76301 / 25) (3686093 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1858061 / 500000) (34725117573 / 500000) (3686093 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1858061 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1858061 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell616 :
    ∀ t ∈ Set.Icc ((43011 / 512000) : ℝ) (43019 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1182950473 / 1000000000) : ℝ) ≤ Real.exp (2 * (43011 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43011 / 512000)) (1182950473 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43019 / 512000) : ℝ)) ≤ (591493721 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43019 / 512000)) (591493721 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((34737204011 / 500000) : ℝ) ≤ Real.exp (3 * (1858119 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1858119 / 500000)) (34737204011 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43011 / 512000) : ℝ) (43019 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1858119 / 500000) (1858237 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43011 / 512000) (43019 / 512000) (1182950473 / 1000000000) (591493721 / 500000000) (1858119 / 500000) (1858237 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43011 / 512000) (43019 / 512000) (1858119 / 500000) (1858237 / 500000) (16471 / 500) (4119 / 125)
    (1299 / 25) (6512 / 125) (-111217 / 200) (47477 / 125000) (3052421 / 1000) (3684811 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1858119 / 500000) (34737204011 / 500000) (3684811 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1858119 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1858119 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell617 :
    ∀ t ∈ Set.Icc ((43019 / 512000) : ℝ) (43027 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1182987441 / 1000000000) : ℝ) ≤ Real.exp (2 * (43019 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43019 / 512000)) (1182987441 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43027 / 512000) : ℝ)) ≤ (118302441 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43027 / 512000)) (118302441 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((69498797807 / 1000000) : ℝ) ≤ Real.exp (3 * (743271 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (743271 / 200000)) (69498797807 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43019 / 512000) : ℝ) (43027 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (743271 / 200000) (371659 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43019 / 512000) (43027 / 512000) (1182987441 / 1000000000) (118302441 / 100000000) (743271 / 200000) (371659 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43019 / 512000) (43027 / 512000) (743271 / 200000) (371659 / 100000) (6589 / 200) (6591 / 200)
    (2079 / 40) (5211 / 100) (-556109 / 1000) (189859 / 500000) (1526401 / 500) (3683517 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (743271 / 200000) (69498797807 / 1000000) (3683517 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (743271 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (743271 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell618 :
    ∀ t ∈ Set.Icc ((43027 / 512000) : ℝ) (8607 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1183024409 / 1000000000) : ℝ) ≤ Real.exp (2 * (43027 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43027 / 512000)) (1183024409 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8607 / 102400) : ℝ)) ≤ (1183061381 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8607 / 102400)) (1183061381 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13904597517 / 200000) : ℝ) ≤ Real.exp (3 * (3716471 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3716471 / 1000000)) (13904597517 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43027 / 512000) : ℝ) (8607 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3716471 / 1000000) (1858353 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43027 / 512000) (8607 / 102400) (1183024409 / 1000000000) (1183061381 / 1000000000) (3716471 / 1000000) (1858353 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43027 / 512000) (8607 / 102400) (3716471 / 1000000) (1858353 / 500000) (8237 / 250) (32957 / 1000)
    (51989 / 1000) (13031 / 250) (-69516 / 125) (379621 / 1000000) (3053183 / 1000) (920559 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3716471 / 1000000) (13904597517 / 200000) (920559 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3716471 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3716471 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell619 :
    ∀ t ∈ Set.Icc ((8607 / 102400) : ℝ) (43043 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((59153069 / 50000000) : ℝ) ≤ Real.exp (2 * (8607 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8607 / 102400)) (59153069 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43043 / 512000) : ℝ)) ≤ (73943647 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43043 / 512000)) (73943647 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((34773592891 / 500000) : ℝ) ≤ Real.exp (3 * (3716587 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3716587 / 1000000)) (34773592891 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8607 / 102400) : ℝ) (43043 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3716587 / 1000000) (1858411 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8607 / 102400) (43043 / 512000) (59153069 / 50000000) (73943647 / 62500000) (3716587 / 1000000) (1858411 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8607 / 102400) (43043 / 512000) (3716587 / 1000000) (1858411 / 500000) (32951 / 1000) (824 / 25)
    (13001 / 250) (26069 / 500) (-556147 / 1000) (15181 / 40000) (610713 / 200) (736191 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3716587 / 1000000) (34773592891 / 500000) (736191 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3716587 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3716587 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch030 :
    ∀ t ∈ Set.Icc ((42883 / 512000) : ℝ) (43043 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell600
      hpThetaDensityLowerExpCompact_cell601)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell602
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell603
      hpThetaDensityLowerExpCompact_cell604)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell605
      hpThetaDensityLowerExpCompact_cell606)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell607
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell608
      hpThetaDensityLowerExpCompact_cell609))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell610
      hpThetaDensityLowerExpCompact_cell611)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell612
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell613
      hpThetaDensityLowerExpCompact_cell614)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell615
      hpThetaDensityLowerExpCompact_cell616)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell617
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell618
      hpThetaDensityLowerExpCompact_cell619)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch030
end HodgeProofHP
