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
theorem hpThetaDensityLowerExpCompact_cell360 :
    ∀ t ∈ Set.Icc ((41579 / 512000) : ℝ) (41583 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((147043977 / 125000000) : ℝ) ≤ Real.exp (2 * (41579 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41579 / 512000)) (147043977 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41583 / 512000) : ℝ)) ≤ (588185099 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41583 / 512000)) (588185099 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65285599579 / 1000000) : ℝ) ≤ Real.exp (3 * (3695509 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3695509 / 1000000)) (65285599579 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41579 / 512000) : ℝ) (41583 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3695509 / 1000000) (739137 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41579 / 512000) (41583 / 512000) (147043977 / 125000000) (588185099 / 500000000) (3695509 / 1000000) (739137 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41579 / 512000) (41583 / 512000) (3695509 / 1000000) (739137 / 200000) (32453 / 1000) (1623 / 50)
    (1236 / 25) (2477 / 50) (-276403 / 500) (1242 / 3125) (1492347 / 500) (3921233 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3695509 / 1000000) (65285599579 / 1000000) (3921233 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3695509 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3695509 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell361 :
    ∀ t ∈ Set.Icc ((41583 / 512000) : ℝ) (41587 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1176370197 / 1000000000) : ℝ) ≤ Real.exp (2 * (41583 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41583 / 512000)) (1176370197 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41587 / 512000) : ℝ)) ≤ (1176388579 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41587 / 512000)) (1176388579 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32648382183 / 500000) : ℝ) ≤ Real.exp (3 * (1847783 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1847783 / 500000)) (32648382183 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41583 / 512000) : ℝ) (41587 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1847783 / 500000) (3695743 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41583 / 512000) (41587 / 512000) (1176370197 / 1000000000) (1176388579 / 1000000000) (1847783 / 500000) (3695743 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41583 / 512000) (41587 / 512000) (1847783 / 500000) (3695743 / 1000000) (16227 / 500) (32461 / 1000)
    (24723 / 500) (49547 / 1000) (-138203 / 250) (397391 / 1000000) (1492441 / 500) (1960281 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1847783 / 500000) (32648382183 / 500000) (1960281 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1847783 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1847783 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell362 :
    ∀ t ∈ Set.Icc ((41587 / 512000) : ℝ) (41591 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((588194289 / 500000000) : ℝ) ≤ Real.exp (2 * (41587 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41587 / 512000)) (588194289 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41591 / 512000) : ℝ)) ≤ (14705087 / 12500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41591 / 512000)) (14705087 / 12500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32654063493 / 500000) : ℝ) ≤ Real.exp (3 * (461953 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (461953 / 125000)) (32654063493 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41587 / 512000) : ℝ) (41591 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (461953 / 125000) (3695801 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41587 / 512000) (41591 / 512000) (588194289 / 500000000) (14705087 / 12500000) (461953 / 125000) (3695801 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41587 / 512000) (41591 / 512000) (461953 / 125000) (3695801 / 1000000) (6491 / 200) (32463 / 1000)
    (49453 / 1000) (24777 / 500) (-276411 / 500) (19867 / 50000) (2985069 / 1000) (97997 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (461953 / 125000) (32654063493 / 500000) (97997 / 25000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461953 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461953 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell363 :
    ∀ t ∈ Set.Icc ((41591 / 512000) : ℝ) (8319 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1176406959 / 1000000000) : ℝ) ≤ Real.exp (2 * (41591 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41591 / 512000)) (1176406959 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8319 / 102400) : ℝ)) ≤ (588212671 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8319 / 102400)) (588212671 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1020617056 / 15625) : ℝ) ≤ Real.exp (3 * (1847841 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1847841 / 500000)) (1020617056 / 15625) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41591 / 512000) : ℝ) (8319 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1847841 / 500000) (1847929 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41591 / 512000) (8319 / 102400) (1176406959 / 1000000000) (588212671 / 500000000) (1847841 / 500000) (1847929 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41591 / 512000) (8319 / 102400) (1847841 / 500000) (1847929 / 500000) (32457 / 1000) (4058 / 125)
    (49461 / 1000) (49561 / 1000) (-552837 / 1000) (39729 / 100000) (2985253 / 1000) (1959599 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1847841 / 500000) (1020617056 / 15625) (1959599 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1847841 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1847841 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell364 :
    ∀ t ∈ Set.Icc ((8319 / 102400) : ℝ) (41599 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1176425341 / 1000000000) : ℝ) ≤ Real.exp (2 * (8319 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8319 / 102400)) (1176425341 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41599 / 512000) : ℝ)) ≤ (1176443723 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41599 / 512000)) (1176443723 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65330858159 / 1000000) : ℝ) ≤ Real.exp (3 * (184787 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (184787 / 50000)) (65330858159 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8319 / 102400) : ℝ) (41599 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (184787 / 50000) (923979 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8319 / 102400) (41599 / 512000) (1176425341 / 1000000000) (1176443723 / 1000000000) (184787 / 50000) (923979 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8319 / 102400) (41599 / 512000) (184787 / 50000) (923979 / 250000) (16229 / 500) (6493 / 200)
    (12367 / 250) (6196 / 125) (-552847 / 1000) (397239 / 1000000) (2985441 / 1000) (979629 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (184787 / 50000) (65330858159 / 1000000) (979629 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (184787 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (184787 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell365 :
    ∀ t ∈ Set.Icc ((41599 / 512000) : ℝ) (41603 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((588221861 / 500000000) : ℝ) ≤ Real.exp (2 * (41599 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41599 / 512000)) (588221861 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41603 / 512000) : ℝ)) ≤ (588231053 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41603 / 512000)) (588231053 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32671015343 / 500000) : ℝ) ≤ Real.exp (3 * (3695797 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3695797 / 1000000)) (32671015343 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41599 / 512000) : ℝ) (41603 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3695797 / 1000000) (1847987 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41599 / 512000) (41603 / 512000) (588221861 / 500000000) (588231053 / 500000000) (3695797 / 1000000) (1847987 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41599 / 512000) (41603 / 512000) (3695797 / 1000000) (1847987 / 500000) (32459 / 1000) (32467 / 1000)
    (24737 / 500) (1983 / 40) (-138213 / 250) (39719 / 100000) (746407 / 250) (1958923 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3695797 / 1000000) (32671015343 / 500000) (1958923 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3695797 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3695797 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell366 :
    ∀ t ∈ Set.Icc ((41603 / 512000) : ℝ) (41607 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235292421 / 200000000) : ℝ) ≤ Real.exp (2 * (41603 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41603 / 512000)) (235292421 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41607 / 512000) : ℝ)) ≤ (147060061 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41607 / 512000)) (147060061 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65353401183 / 1000000) : ℝ) ≤ Real.exp (3 * (739171 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (739171 / 200000)) (65353401183 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41603 / 512000) : ℝ) (41607 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (739171 / 200000) (115501 / 31250) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41603 / 512000) (41607 / 512000) (235292421 / 200000000) (147060061 / 125000000) (739171 / 200000) (115501 / 31250) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41603 / 512000) (41607 / 512000) (739171 / 200000) (115501 / 31250) (32461 / 1000) (8117 / 250)
    (49481 / 1000) (24791 / 500) (-552863 / 1000) (19857 / 50000) (597163 / 200) (783433 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (739171 / 200000) (65353401183 / 1000000) (783433 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (739171 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (739171 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell367 :
    ∀ t ∈ Set.Icc ((41607 / 512000) : ℝ) (41611 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1176480487 / 1000000000) : ℝ) ≤ Real.exp (2 * (41607 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41607 / 512000)) (1176480487 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41611 / 512000) : ℝ)) ≤ (1176498871 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41611 / 512000)) (1176498871 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65364773659 / 1000000) : ℝ) ≤ Real.exp (3 * (3695913 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3695913 / 1000000)) (65364773659 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41607 / 512000) : ℝ) (41611 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3695913 / 1000000) (3696089 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41607 / 512000) (41611 / 512000) (1176480487 / 1000000000) (1176498871 / 1000000000) (3695913 / 1000000) (3696089 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41607 / 512000) (41611 / 512000) (3695913 / 1000000) (3696089 / 1000000) (16231 / 500) (32469 / 1000)
    (49489 / 1000) (49589 / 1000) (-552877 / 1000) (397089 / 1000000) (2986) (3916483 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3695913 / 1000000) (65364773659 / 1000000) (3916483 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3695913 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3695913 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell368 :
    ∀ t ∈ Set.Icc ((41611 / 512000) : ℝ) (8323 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((117649887 / 100000000) : ℝ) ≤ Real.exp (2 * (41611 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41611 / 512000)) (117649887 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8323 / 102400) : ℝ)) ≤ (1176517253 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8323 / 102400)) (1176517253 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32688074057 / 500000) : ℝ) ≤ Real.exp (3 * (3695971 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3695971 / 1000000)) (32688074057 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41611 / 512000) : ℝ) (8323 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3695971 / 1000000) (3696147 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41611 / 512000) (8323 / 102400) (117649887 / 100000000) (1176517253 / 1000000000) (3695971 / 1000000) (3696147 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41611 / 512000) (8323 / 102400) (3695971 / 1000000) (3696147 / 1000000) (32463 / 1000) (32471 / 1000)
    (6187 / 125) (12399 / 250) (-552887 / 1000) (397039 / 1000000) (2986187 / 1000) (1957901 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3695971 / 1000000) (32688074057 / 500000) (1957901 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3695971 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3695971 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell369 :
    ∀ t ∈ Set.Icc ((8323 / 102400) : ℝ) (41619 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((294129313 / 250000000) : ℝ) ≤ Real.exp (2 * (8323 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8323 / 102400)) (294129313 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41619 / 512000) : ℝ)) ≤ (1176535637 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41619 / 512000)) (1176535637 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32693664193 / 500000) : ℝ) ≤ Real.exp (3 * (924007 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (924007 / 250000)) (32693664193 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8323 / 102400) : ℝ) (41619 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (924007 / 250000) (739241 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8323 / 102400) (41619 / 512000) (294129313 / 250000000) (1176535637 / 1000000000) (924007 / 250000) (739241 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8323 / 102400) (41619 / 512000) (924007 / 250000) (739241 / 200000) (6493 / 200) (4059 / 125)
    (24751 / 500) (49603 / 1000) (-552893 / 1000) (396989 / 1000000) (1493187 / 500) (978783 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (924007 / 250000) (32693664193 / 500000) (978783 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (924007 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (924007 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell370 :
    ∀ t ∈ Set.Icc ((41619 / 512000) : ℝ) (41623 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((294133909 / 250000000) : ℝ) ≤ Real.exp (2 * (41619 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41619 / 512000)) (294133909 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41623 / 512000) : ℝ)) ≤ (58827701 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41623 / 512000)) (58827701 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32699353383 / 500000) : ℝ) ≤ Real.exp (3 * (1848043 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1848043 / 500000)) (32699353383 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41619 / 512000) : ℝ) (41623 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1848043 / 500000) (3696263 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41619 / 512000) (41623 / 512000) (294133909 / 250000000) (58827701 / 50000000) (1848043 / 500000) (3696263 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41619 / 512000) (41623 / 512000) (1848043 / 500000) (3696263 / 1000000) (16233 / 500) (32473 / 1000)
    (49509 / 1000) (4961 / 100) (-552903 / 1000) (396939 / 1000000) (1493281 / 500) (3914451 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1848043 / 500000) (32699353383 / 500000) (3914451 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1848043 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1848043 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell371 :
    ∀ t ∈ Set.Icc ((41623 / 512000) : ℝ) (41627 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1176554019 / 1000000000) : ℝ) ≤ Real.exp (2 * (41623 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41623 / 512000)) (1176554019 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41627 / 512000) : ℝ)) ≤ (294143101 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41627 / 512000)) (294143101 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32705043563 / 500000) : ℝ) ≤ Real.exp (3 * (231009 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (231009 / 62500)) (32705043563 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41623 / 512000) : ℝ) (41627 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (231009 / 62500) (11551 / 3125) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41623 / 512000) (41627 / 512000) (1176554019 / 1000000000) (294143101 / 250000000) (231009 / 62500) (11551 / 3125) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41623 / 512000) (41627 / 512000) (231009 / 62500) (11551 / 3125) (8117 / 250) (1299 / 40)
    (49517 / 1000) (49617 / 1000) (-276459 / 500) (49611 / 125000) (1493373 / 500) (391377 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (231009 / 62500) (32705043563 / 500000) (391377 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (231009 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (231009 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell372 :
    ∀ t ∈ Set.Icc ((41627 / 512000) : ℝ) (41631 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1176572403 / 1000000000) : ℝ) ≤ Real.exp (2 * (41627 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41627 / 512000)) (1176572403 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41631 / 512000) : ℝ)) ≤ (294147697 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41631 / 512000)) (294147697 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32710734733 / 500000) : ℝ) ≤ Real.exp (3 * (1848101 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1848101 / 500000)) (32710734733 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41627 / 512000) : ℝ) (41631 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1848101 / 500000) (1848189 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41627 / 512000) (41631 / 512000) (1176572403 / 1000000000) (294147697 / 250000000) (1848101 / 500000) (1848189 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41627 / 512000) (41631 / 512000) (1848101 / 500000) (1848189 / 500000) (32469 / 1000) (8119 / 250)
    (12381 / 250) (6203 / 125) (-69116 / 125) (198419 / 500000) (1493467 / 500) (3913089 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1848101 / 500000) (32710734733 / 500000) (3913089 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1848101 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1848101 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell373 :
    ∀ t ∈ Set.Icc ((41631 / 512000) : ℝ) (8327 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1176590787 / 1000000000) : ℝ) ≤ Real.exp (2 * (41631 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41631 / 512000)) (1176590787 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8327 / 102400) : ℝ)) ≤ (294152293 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8327 / 102400)) (294152293 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65432657489 / 1000000) : ℝ) ≤ Real.exp (3 * (3696259 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3696259 / 1000000)) (65432657489 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41631 / 512000) : ℝ) (8327 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3696259 / 1000000) (924109 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41631 / 512000) (8327 / 102400) (1176590787 / 1000000000) (294152293 / 250000000) (3696259 / 1000000) (924109 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41631 / 512000) (8327 / 102400) (3696259 / 1000000) (924109 / 250000) (3247 / 100) (16239 / 500)
    (4953 / 100) (49631 / 1000) (-276467 / 500) (396789 / 1000000) (2987121 / 1000) (195621 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3696259 / 1000000) (65432657489 / 1000000) (195621 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3696259 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3696259 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell374 :
    ∀ t ∈ Set.Icc ((8327 / 102400) : ℝ) (41639 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1176609171 / 1000000000) : ℝ) ≤ Real.exp (2 * (8327 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8327 / 102400)) (1176609171 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41639 / 512000) : ℝ)) ≤ (1176627557 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41639 / 512000)) (1176627557 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65444043757 / 1000000) : ℝ) ≤ Real.exp (3 * (3696317 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3696317 / 1000000)) (65444043757 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8327 / 102400) : ℝ) (41639 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3696317 / 1000000) (1848247 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8327 / 102400) (41639 / 512000) (1176609171 / 1000000000) (1176627557 / 1000000000) (3696317 / 1000000) (1848247 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8327 / 102400) (41639 / 512000) (3696317 / 1000000) (1848247 / 500000) (4059 / 125) (32479 / 1000)
    (49537 / 1000) (24819 / 500) (-69118 / 125) (198369 / 500000) (2987309 / 1000) (3911739 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3696317 / 1000000) (65444043757 / 1000000) (3911739 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3696317 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3696317 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell375 :
    ∀ t ∈ Set.Icc ((41639 / 512000) : ℝ) (41643 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((294156889 / 250000000) : ℝ) ≤ Real.exp (2 * (41639 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41639 / 512000)) (294156889 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41643 / 512000) : ℝ)) ≤ (588322971 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41643 / 512000)) (588322971 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32727716003 / 500000) : ℝ) ≤ Real.exp (3 * (29571 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (29571 / 8000)) (32727716003 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41639 / 512000) : ℝ) (41643 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (29571 / 8000) (3696551 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41639 / 512000) (41643 / 512000) (294156889 / 250000000) (588322971 / 500000000) (29571 / 8000) (3696551 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41639 / 512000) (41643 / 512000) (29571 / 8000) (3696551 / 1000000) (32473 / 1000) (812 / 25)
    (9909 / 200) (9929 / 200) (-276479 / 500) (24793 / 62500) (2987493 / 1000) (3911059 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (29571 / 8000) (32727716003 / 500000) (3911059 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (29571 / 8000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (29571 / 8000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell376 :
    ∀ t ∈ Set.Icc ((41643 / 512000) : ℝ) (41647 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1176645941 / 1000000000) : ℝ) ≤ Real.exp (2 * (41643 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41643 / 512000)) (1176645941 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41647 / 512000) : ℝ)) ≤ (1176664327 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41647 / 512000)) (1176664327 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65466822237 / 1000000) : ℝ) ≤ Real.exp (3 * (3696433 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3696433 / 1000000)) (65466822237 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41643 / 512000) : ℝ) (41647 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3696433 / 1000000) (3696609 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41643 / 512000) (41647 / 512000) (1176645941 / 1000000000) (1176664327 / 1000000000) (3696433 / 1000000) (3696609 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41643 / 512000) (41647 / 512000) (3696433 / 1000000) (3696609 / 1000000) (16237 / 500) (16241 / 500)
    (6194 / 125) (12413 / 250) (-552969 / 1000) (396637 / 1000000) (74692 / 25) (1955189 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3696433 / 1000000) (65466822237 / 1000000) (1955189 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3696433 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3696433 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell377 :
    ∀ t ∈ Set.Icc ((41647 / 512000) : ℝ) (41651 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((588332163 / 500000000) : ℝ) ≤ Real.exp (2 * (41647 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41647 / 512000)) (588332163 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41651 / 512000) : ℝ)) ≤ (1176682713 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41651 / 512000)) (1176682713 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13095603603 / 200000) : ℝ) ≤ Real.exp (3 * (369649 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (369649 / 100000)) (13095603603 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41647 / 512000) : ℝ) (41651 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (369649 / 100000) (3696667 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41647 / 512000) (41651 / 512000) (588332163 / 500000000) (1176682713 / 1000000000) (369649 / 100000) (3696667 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41647 / 512000) (41651 / 512000) (369649 / 100000) (3696667 / 1000000) (8119 / 250) (32483 / 1000)
    (24779 / 500) (49659 / 1000) (-276487 / 500) (99147 / 250000) (746967 / 250) (390971 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (369649 / 100000) (13095603603 / 200000) (390971 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (369649 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (369649 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell378 :
    ∀ t ∈ Set.Icc ((41651 / 512000) : ℝ) (8331 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((147085339 / 125000000) : ℝ) ≤ Real.exp (2 * (41651 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41651 / 512000)) (147085339 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8331 / 102400) : ℝ)) ≤ (1176701099 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8331 / 102400)) (1176701099 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65489412177 / 1000000) : ℝ) ≤ Real.exp (3 * (924137 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (924137 / 250000)) (65489412177 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41651 / 512000) : ℝ) (8331 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (924137 / 250000) (147869 / 40000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41651 / 512000) (8331 / 102400) (147085339 / 125000000) (1176701099 / 1000000000) (924137 / 250000) (147869 / 40000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41651 / 512000) (8331 / 102400) (924137 / 250000) (147869 / 40000) (32477 / 1000) (8121 / 250)
    (9913 / 200) (24833 / 500) (-69123 / 125) (198269 / 500000) (597611 / 200) (3909029 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (924137 / 250000) (65489412177 / 1000000) (3909029 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (924137 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (924137 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell379 :
    ∀ t ∈ Set.Icc ((8331 / 102400) : ℝ) (41659 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((588350549 / 500000000) : ℝ) ≤ Real.exp (2 * (8331 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8331 / 102400)) (588350549 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41659 / 512000) : ℝ)) ≤ (235343897 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41659 / 512000)) (235343897 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65500808321 / 1000000) : ℝ) ≤ Real.exp (3 * (1848303 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1848303 / 500000)) (65500808321 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8331 / 102400) : ℝ) (41659 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1848303 / 500000) (1848391 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8331 / 102400) (41659 / 512000) (588350549 / 500000000) (235343897 / 200000000) (1848303 / 500000) (1848391 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8331 / 102400) (41659 / 512000) (1848303 / 500000) (1848391 / 500000) (16239 / 500) (16243 / 500)
    (49573 / 1000) (49673 / 1000) (-552999 / 1000) (396487 / 1000000) (74706 / 25) (3908349 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1848303 / 500000) (65500808321 / 1000000) (3908349 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1848303 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1848303 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch018 :
    ∀ t ∈ Set.Icc ((41579 / 512000) : ℝ) (41659 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell360
      hpThetaDensityLowerExpCompact_cell361)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell362
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell363
      hpThetaDensityLowerExpCompact_cell364)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell365
      hpThetaDensityLowerExpCompact_cell366)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell367
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell368
      hpThetaDensityLowerExpCompact_cell369))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell370
      hpThetaDensityLowerExpCompact_cell371)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell372
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell373
      hpThetaDensityLowerExpCompact_cell374)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell375
      hpThetaDensityLowerExpCompact_cell376)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell377
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell378
      hpThetaDensityLowerExpCompact_cell379)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch018
end HodgeProofHP
