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
theorem hpThetaDensityLowerExpCompact_cell580 :
    ∀ t ∈ Set.Icc ((42723 / 512000) : ℝ) (42731 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((590810201 / 500000000) : ℝ) ≤ Real.exp (2 * (42723 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42723 / 512000)) (590810201 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42731 / 512000) : ℝ)) ≤ (1181657329 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42731 / 512000)) (1181657329 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((68609050751 / 1000000) : ℝ) ≤ Real.exp (3 * (185603 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (185603 / 50000)) (68609050751 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42723 / 512000) : ℝ) (42731 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (185603 / 50000) (742459 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42723 / 512000) (42731 / 512000) (590810201 / 500000000) (1181657329 / 1000000000) (185603 / 50000) (742459 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42723 / 512000) (42731 / 512000) (185603 / 50000) (742459 / 200000) (32843 / 1000) (32853 / 1000)
    (25723 / 500) (2579 / 50) (-555391 / 1000) (38331 / 100000) (607743 / 200) (3731287 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (185603 / 50000) (68609050751 / 1000000) (3731287 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (185603 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (185603 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell581 :
    ∀ t ∈ Set.Icc ((42731 / 512000) : ℝ) (42739 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((73853583 / 62500000) : ℝ) ≤ Real.exp (2 * (42731 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42731 / 512000)) (73853583 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42739 / 512000) : ℝ)) ≤ (73855891 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42739 / 512000)) (73855891 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((68632930843 / 1000000) : ℝ) ≤ Real.exp (3 * (232011 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (232011 / 62500)) (68632930843 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42731 / 512000) : ℝ) (42739 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (232011 / 62500) (3712411 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42731 / 512000) (42739 / 512000) (73853583 / 62500000) (73855891 / 62500000) (232011 / 62500) (3712411 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42731 / 512000) (42739 / 512000) (232011 / 62500) (3712411 / 1000000) (16423 / 500) (6571 / 200)
    (2573 / 50) (10319 / 200) (-555411 / 1000) (383213 / 1000000) (607819 / 200) (932497 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (232011 / 62500) (68632930843 / 1000000) (932497 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (232011 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (232011 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell582 :
    ∀ t ∈ Set.Icc ((42739 / 512000) : ℝ) (42747 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((236338851 / 200000000) : ℝ) ≤ Real.exp (2 * (42739 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42739 / 512000)) (236338851 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42747 / 512000) : ℝ)) ≤ (236346237 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42747 / 512000)) (236346237 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4291051203 / 62500) : ℝ) ≤ Real.exp (3 * (928073 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (928073 / 250000)) (4291051203 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42739 / 512000) : ℝ) (42747 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (928073 / 250000) (3712527 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42739 / 512000) (42747 / 512000) (236338851 / 200000000) (236346237 / 200000000) (928073 / 250000) (3712527 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42739 / 512000) (42747 / 512000) (928073 / 250000) (3712527 / 1000000) (32849 / 1000) (16429 / 500)
    (25737 / 500) (51609 / 1000) (-55543 / 100) (76623 / 200000) (121579 / 40) (3728691 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (928073 / 250000) (4291051203 / 62500) (3728691 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (928073 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (928073 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell583 :
    ∀ t ∈ Set.Icc ((42747 / 512000) : ℝ) (8551 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((73858199 / 62500000) : ℝ) ≤ Real.exp (2 * (42747 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42747 / 512000)) (73858199 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8551 / 102400) : ℝ)) ≤ (236353623 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8551 / 102400)) (236353623 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((68680715967 / 1000000) : ℝ) ≤ Real.exp (3 * (464051 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (464051 / 125000)) (68680715967 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42747 / 512000) : ℝ) (8551 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (464051 / 125000) (3712643 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42747 / 512000) (8551 / 102400) (73858199 / 62500000) (236353623 / 200000000) (464051 / 125000) (3712643 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42747 / 512000) (8551 / 102400) (464051 / 125000) (3712643 / 1000000) (8213 / 250) (32861 / 1000)
    (51489 / 1000) (51623 / 1000) (-11109 / 20) (191509 / 500000) (607971 / 200) (3727393 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (464051 / 125000) (68680715967 / 1000000) (3727393 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (464051 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (464051 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell584 :
    ∀ t ∈ Set.Icc ((8551 / 102400) : ℝ) (42763 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((590884057 / 500000000) : ℝ) ≤ Real.exp (2 * (8551 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8551 / 102400)) (590884057 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42763 / 512000) : ℝ)) ≤ (236361009 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42763 / 512000)) (236361009 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((68704621003 / 1000000) : ℝ) ≤ Real.exp (3 * (928131 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (928131 / 250000)) (68704621003 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8551 / 102400) : ℝ) (42763 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (928131 / 250000) (3712759 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8551 / 102400) (42763 / 512000) (590884057 / 500000000) (236361009 / 200000000) (928131 / 250000) (3712759 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8551 / 102400) (42763 / 512000) (928131 / 250000) (3712759 / 1000000) (16427 / 500) (4108 / 125)
    (51503 / 1000) (51637 / 1000) (-555469 / 1000) (9573 / 25000) (608047 / 200) (232881 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (928131 / 250000) (68704621003 / 1000000) (232881 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (928131 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (928131 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell585 :
    ∀ t ∈ Set.Icc ((42763 / 512000) : ℝ) (42771 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((295451261 / 250000000) : ℝ) ≤ Real.exp (2 * (42763 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42763 / 512000)) (295451261 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42771 / 512000) : ℝ)) ≤ (1181841977 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42771 / 512000)) (1181841977 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1718213359 / 25000) : ℝ) ≤ Real.exp (3 * (11602 / 3125)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (11602 / 3125)) (1718213359 / 25000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42763 / 512000) : ℝ) (42771 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (11602 / 3125) (29703 / 8000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42763 / 512000) (42771 / 512000) (295451261 / 250000000) (1181841977 / 1000000000) (11602 / 3125) (29703 / 8000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42763 / 512000) (42771 / 512000) (11602 / 3125) (29703 / 8000) (32857 / 1000) (16433 / 500)
    (51517 / 1000) (12913 / 250) (-555489 / 1000) (382823 / 1000000) (608123 / 200) (291 / 78125)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (11602 / 3125) (1718213359 / 25000) (291 / 78125)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (11602 / 3125)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (11602 / 3125)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell586 :
    ∀ t ∈ Set.Icc ((42771 / 512000) : ℝ) (42779 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((147730247 / 125000000) : ℝ) ≤ Real.exp (2 * (42771 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42771 / 512000)) (147730247 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42779 / 512000) : ℝ)) ≤ (1181878911 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42779 / 512000)) (1181878911 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1718811401 / 25000) : ℝ) ≤ Real.exp (3 * (928189 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (928189 / 250000)) (1718811401 / 25000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42771 / 512000) : ℝ) (42779 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (928189 / 250000) (3712991 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42771 / 512000) (42779 / 512000) (147730247 / 125000000) (1181878911 / 1000000000) (928189 / 250000) (3712991 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42771 / 512000) (42779 / 512000) (928189 / 250000) (3712991 / 1000000) (1643 / 50) (32869 / 1000)
    (51531 / 1000) (25833 / 500) (-138877 / 250) (191363 / 500000) (608199 / 200) (232719 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (928189 / 250000) (1718811401 / 25000) (232719 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (928189 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (928189 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell587 :
    ∀ t ∈ Set.Icc ((42779 / 512000) : ℝ) (42787 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((118187891 / 100000000) : ℝ) ≤ Real.exp (2 * (42779 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42779 / 512000)) (118187891 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42787 / 512000) : ℝ)) ≤ (236383169 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42787 / 512000)) (236383169 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((34388193023 / 500000) : ℝ) ≤ Real.exp (3 * (464109 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (464109 / 125000)) (34388193023 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42779 / 512000) : ℝ) (42787 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (464109 / 125000) (3713107 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42779 / 512000) (42787 / 512000) (118187891 / 100000000) (236383169 / 200000000) (464109 / 125000) (3713107 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42779 / 512000) (42787 / 512000) (464109 / 125000) (3713107 / 1000000) (32863 / 1000) (4109 / 125)
    (25773 / 500) (1292 / 25) (-555527 / 1000) (95657 / 250000) (24331 / 8) (116319 / 31250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (464109 / 125000) (34388193023 / 500000) (116319 / 31250000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (464109 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (464109 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell588 :
    ∀ t ∈ Set.Icc ((42787 / 512000) : ℝ) (8559 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((295478961 / 250000000) : ℝ) ≤ Real.exp (2 * (42787 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42787 / 512000)) (295478961 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8559 / 102400) : ℝ)) ≤ (59097639 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8559 / 102400)) (59097639 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((34400162191 / 500000) : ℝ) ≤ Real.exp (3 * (928247 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (928247 / 250000)) (34400162191 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42787 / 512000) : ℝ) (8559 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (928247 / 250000) (3713223 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42787 / 512000) (8559 / 102400) (295478961 / 250000000) (59097639 / 50000000) (928247 / 250000) (3713223 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42787 / 512000) (8559 / 102400) (928247 / 250000) (3713223 / 1000000) (6573 / 200) (263 / 8)
    (1289 / 25) (10339 / 200) (-555547 / 1000) (382531 / 1000000) (608351 / 200) (3720913 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (928247 / 250000) (34400162191 / 500000) (3720913 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (928247 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (928247 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell589 :
    ∀ t ∈ Set.Icc ((8559 / 102400) : ℝ) (42803 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1181952779 / 1000000000) : ℝ) ≤ Real.exp (2 * (8559 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8559 / 102400)) (1181952779 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42803 / 512000) : ℝ)) ≤ (1181989717 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42803 / 512000)) (1181989717 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((68824271049 / 1000000) : ℝ) ≤ Real.exp (3 * (232069 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (232069 / 62500)) (68824271049 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8559 / 102400) : ℝ) (42803 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (232069 / 62500) (3713339 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8559 / 102400) (42803 / 512000) (1181952779 / 1000000000) (1181989717 / 1000000000) (232069 / 62500) (3713339 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8559 / 102400) (42803 / 512000) (232069 / 62500) (3713339 / 1000000) (8217 / 250) (32877 / 1000)
    (25787 / 500) (51709 / 1000) (-277783 / 500) (191217 / 500000) (608427 / 200) (3719619 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (232069 / 62500) (68824271049 / 1000000) (3719619 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (232069 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (232069 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell590 :
    ∀ t ∈ Set.Icc ((42803 / 512000) : ℝ) (42811 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((295497429 / 250000000) : ℝ) ≤ Real.exp (2 * (42803 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42803 / 512000)) (295497429 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42811 / 512000) : ℝ)) ≤ (236405331 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42811 / 512000)) (236405331 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((68848226051 / 1000000) : ℝ) ≤ Real.exp (3 * (185661 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (185661 / 50000)) (68848226051 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42803 / 512000) : ℝ) (42811 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (185661 / 50000) (742691 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42803 / 512000) (42811 / 512000) (295497429 / 250000000) (236405331 / 200000000) (185661 / 50000) (742691 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42803 / 512000) (42811 / 512000) (185661 / 50000) (742691 / 200000) (32871 / 1000) (822 / 25)
    (12897 / 250) (51723 / 1000) (-277793 / 500) (382337 / 1000000) (608503 / 200) (929581 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (185661 / 50000) (68848226051 / 1000000) (929581 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (185661 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (185661 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell591 :
    ∀ t ∈ Set.Icc ((42811 / 512000) : ℝ) (42819 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((591013327 / 500000000) : ℝ) ≤ Real.exp (2 * (42811 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42811 / 512000)) (591013327 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42819 / 512000) : ℝ)) ≤ (591031797 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42819 / 512000)) (591031797 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((68872189391 / 1000000) : ℝ) ≤ Real.exp (3 * (464167 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (464167 / 125000)) (68872189391 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42811 / 512000) : ℝ) (42819 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (464167 / 125000) (3713571 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42811 / 512000) (42819 / 512000) (591013327 / 500000000) (591031797 / 500000000) (464167 / 125000) (3713571 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42811 / 512000) (42819 / 512000) (464167 / 125000) (3713571 / 1000000) (16437 / 500) (32883 / 1000)
    (51603 / 1000) (51737 / 1000) (-111121 / 200) (2389 / 6250) (608579 / 200) (3717031 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (464167 / 125000) (68872189391 / 1000000) (3717031 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (464167 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (464167 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell592 :
    ∀ t ∈ Set.Icc ((42819 / 512000) : ℝ) (42827 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1182063593 / 1000000000) : ℝ) ≤ Real.exp (2 * (42819 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42819 / 512000)) (1182063593 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42827 / 512000) : ℝ)) ≤ (591050267 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42827 / 512000)) (591050267 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4306010067 / 62500) : ℝ) ≤ Real.exp (3 * (928363 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (928363 / 250000)) (4306010067 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42819 / 512000) : ℝ) (42827 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (928363 / 250000) (464211 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42819 / 512000) (42827 / 512000) (1182063593 / 1000000000) (591050267 / 500000000) (928363 / 250000) (464211 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42819 / 512000) (42827 / 512000) (928363 / 250000) (464211 / 125000) (8219 / 250) (16443 / 500)
    (51617 / 1000) (6469 / 125) (-27781 / 50) (382143 / 1000000) (3043279 / 1000) (3715737 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (928363 / 250000) (4306010067 / 62500) (3715737 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (928363 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (928363 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell593 :
    ∀ t ∈ Set.Icc ((42827 / 512000) : ℝ) (8567 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1182100533 / 1000000000) : ℝ) ≤ Real.exp (2 * (42827 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42827 / 512000)) (1182100533 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8567 / 102400) : ℝ)) ≤ (47285499 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8567 / 102400)) (47285499 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8615017637 / 125000) : ℝ) ≤ Real.exp (3 * (116049 / 31250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (116049 / 31250)) (8615017637 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42827 / 512000) : ℝ) (8567 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (116049 / 31250) (928451 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42827 / 512000) (8567 / 102400) (1182100533 / 1000000000) (47285499 / 40000000) (116049 / 31250) (928451 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42827 / 512000) (8567 / 102400) (116049 / 31250) (928451 / 250000) (32879 / 1000) (4111 / 125)
    (51631 / 1000) (25883 / 500) (-13891 / 25) (76409 / 200000) (3043659 / 1000) (928611 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (116049 / 31250) (8615017637 / 125000) (928611 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (116049 / 31250)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (116049 / 31250)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell594 :
    ∀ t ∈ Set.Icc ((8567 / 102400) : ℝ) (42843 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((591068737 / 500000000) : ℝ) ≤ Real.exp (2 * (8567 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8567 / 102400)) (591068737 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42843 / 512000) : ℝ)) ≤ (1182174417 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42843 / 512000)) (1182174417 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((68944129467 / 1000000) : ℝ) ≤ Real.exp (3 * (928421 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (928421 / 250000)) (68944129467 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8567 / 102400) : ℝ) (42843 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (928421 / 250000) (11606 / 3125) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8567 / 102400) (42843 / 512000) (591068737 / 500000000) (1182174417 / 1000000000) (928421 / 250000) (11606 / 3125) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8567 / 102400) (42843 / 512000) (928421 / 250000) (11606 / 3125) (16441 / 500) (32891 / 1000)
    (10329 / 200) (51781 / 1000) (-555659 / 1000) (95487 / 250000) (3044039 / 1000) (29009 / 7812500)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (928421 / 250000) (68944129467 / 1000000) (29009 / 7812500)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (928421 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (928421 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell595 :
    ∀ t ∈ Set.Icc ((42843 / 512000) : ℝ) (42851 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((73885901 / 62500000) : ℝ) ≤ Real.exp (2 * (42843 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42843 / 512000)) (73885901 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42851 / 512000) : ℝ)) ≤ (1182211361 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42851 / 512000)) (1182211361 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((68968126187 / 1000000) : ℝ) ≤ Real.exp (3 * (18569 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (18569 / 5000)) (68968126187 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42843 / 512000) : ℝ) (42851 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (18569 / 5000) (928509 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42843 / 512000) (42851 / 512000) (73885901 / 62500000) (1182211361 / 1000000000) (18569 / 5000) (928509 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42843 / 512000) (42851 / 512000) (18569 / 5000) (928509 / 250000) (6577 / 200) (16447 / 500)
    (2583 / 50) (10359 / 200) (-277839 / 500) (381851 / 1000000) (3044419 / 1000) (185593 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (18569 / 5000) (68968126187 / 1000000) (185593 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (18569 / 5000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (18569 / 5000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell596 :
    ∀ t ∈ Set.Icc ((42851 / 512000) : ℝ) (42859 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((7388821 / 6250000) : ℝ) ≤ Real.exp (2 * (42851 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42851 / 512000)) (7388821 / 6250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42859 / 512000) : ℝ)) ≤ (236449661 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42859 / 512000)) (236449661 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3449606563 / 50000) : ℝ) ≤ Real.exp (3 * (928479 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (928479 / 250000)) (3449606563 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42851 / 512000) : ℝ) (42859 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (928479 / 250000) (464269 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42851 / 512000) (42859 / 512000) (7388821 / 6250000) (236449661 / 200000000) (928479 / 250000) (464269 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42851 / 512000) (42859 / 512000) (928479 / 250000) (464269 / 125000) (32887 / 1000) (32897 / 1000)
    (25837 / 500) (51809 / 1000) (-277849 / 500) (190877 / 500000) (15224 / 5) (3710569 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (928479 / 250000) (3449606563 / 50000) (3710569 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (928479 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (928479 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell597 :
    ∀ t ∈ Set.Icc ((42859 / 512000) : ℝ) (42867 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((73890519 / 62500000) : ℝ) ≤ Real.exp (2 * (42859 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42859 / 512000)) (73890519 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42867 / 512000) : ℝ)) ≤ (1182285251 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42867 / 512000)) (1182285251 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8627043967 / 125000) : ℝ) ≤ Real.exp (3 * (3714033 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3714033 / 1000000)) (8627043967 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42859 / 512000) : ℝ) (42867 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3714033 / 1000000) (928567 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42859 / 512000) (42867 / 512000) (73890519 / 62500000) (1182285251 / 1000000000) (3714033 / 1000000) (928567 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42859 / 512000) (42867 / 512000) (3714033 / 1000000) (928567 / 250000) (3289 / 100) (32899 / 1000)
    (51689 / 1000) (51823 / 1000) (-277861 / 500) (47707 / 125000) (152259 / 50) (1854633 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3714033 / 1000000) (8627043967 / 125000) (1854633 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3714033 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3714033 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell598 :
    ∀ t ∈ Set.Icc ((42867 / 512000) : ℝ) (343 / 4096), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((4729141 / 4000000) : ℝ) ≤ Real.exp (2 * (42867 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42867 / 512000)) (4729141 / 4000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((343 / 4096) : ℝ)) ≤ (591161099 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (343 / 4096)) (591161099 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((34520186797 / 500000) : ℝ) ≤ Real.exp (3 * (3714149 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3714149 / 1000000)) (34520186797 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42867 / 512000) : ℝ) (343 / 4096),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3714149 / 1000000) (232149 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42867 / 512000) (343 / 4096) (4729141 / 4000000) (591161099 / 500000000) (3714149 / 1000000) (232149 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42867 / 512000) (343 / 4096) (3714149 / 1000000) (232149 / 62500) (32893 / 1000) (16451 / 500)
    (51703 / 1000) (25919 / 500) (-555741 / 1000) (381559 / 1000000) (3045561 / 1000) (463497 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3714149 / 1000000) (34520186797 / 500000) (463497 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3714149 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3714149 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell599 :
    ∀ t ∈ Set.Icc ((343 / 4096) : ℝ) (42883 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1182322197 / 1000000000) : ℝ) ≤ Real.exp (2 * (343 / 4096)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (343 / 4096)) (1182322197 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42883 / 512000) : ℝ)) ≤ (591179573 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42883 / 512000)) (591179573 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((69064403813 / 1000000) : ℝ) ≤ Real.exp (3 * (742853 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (742853 / 200000)) (69064403813 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((343 / 4096) : ℝ) (42883 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (742853 / 200000) (7429 / 2000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (343 / 4096) (42883 / 512000) (1182322197 / 1000000000) (591179573 / 500000000) (742853 / 200000) (7429 / 2000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (343 / 4096) (42883 / 512000) (742853 / 200000) (7429 / 2000) (4112 / 125) (6581 / 200)
    (51717 / 1000) (12963 / 250) (-555761 / 1000) (190731 / 500000) (3045941 / 1000) (1853343 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (742853 / 200000) (69064403813 / 1000000) (1853343 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (742853 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (742853 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch029 :
    ∀ t ∈ Set.Icc ((42723 / 512000) : ℝ) (42883 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell580
      hpThetaDensityLowerExpCompact_cell581)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell582
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell583
      hpThetaDensityLowerExpCompact_cell584)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell585
      hpThetaDensityLowerExpCompact_cell586)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell587
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell588
      hpThetaDensityLowerExpCompact_cell589))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell590
      hpThetaDensityLowerExpCompact_cell591)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell592
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell593
      hpThetaDensityLowerExpCompact_cell594)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell595
      hpThetaDensityLowerExpCompact_cell596)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell597
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell598
      hpThetaDensityLowerExpCompact_cell599)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch029
end HodgeProofHP
