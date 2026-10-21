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
theorem hpThetaDensityLowerExpCompact_cell980 :
    ∀ t ∈ Set.Icc ((50067 / 512000) : ℝ) (50099 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1216009041 / 1000000000) : ℝ) ≤ Real.exp (2 * (50067 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (50067 / 512000)) (1216009041 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((50099 / 512000) : ℝ)) ≤ (304040263 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (50099 / 512000)) (304040263 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((23717801457 / 250000) : ℝ) ≤ Real.exp (3 * (955023 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (955023 / 250000)) (23717801457 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((50067 / 512000) : ℝ) (50099 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (955023 / 250000) (955173 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (50067 / 512000) (50099 / 512000) (1216009041 / 1000000000) (304040263 / 250000000) (955023 / 250000) (955173 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (50067 / 512000) (50099 / 512000) (955023 / 250000) (955173 / 250000) (4431 / 125) (35471 / 1000)
    (32673 / 500) (8213 / 125) (-284409 / 500) (302201 / 1000000) (85237 / 25) (674599 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (955023 / 250000) (23717801457 / 250000) (674599 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (955023 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (955023 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell981 :
    ∀ t ∈ Set.Icc ((50099 / 512000) : ℝ) (50131 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1216161051 / 1000000000) : ℝ) ≤ Real.exp (2 * (50099 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (50099 / 512000)) (1216161051 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((50131 / 512000) : ℝ)) ≤ (608156541 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (50131 / 512000)) (608156541 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((23751765897 / 250000) : ℝ) ≤ Real.exp (3 * (3820569 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3820569 / 1000000)) (23751765897 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((50099 / 512000) : ℝ) (50131 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3820569 / 1000000) (382117 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (50099 / 512000) (50131 / 512000) (1216161051 / 1000000000) (608156541 / 500000000) (3820569 / 1000000) (382117 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (50099 / 512000) (50131 / 512000) (3820569 / 1000000) (382117 / 100000) (35459 / 1000) (17741 / 500)
    (65411 / 1000) (65769 / 1000) (-284433 / 500) (150941 / 500000) (3411187 / 1000) (2694537 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3820569 / 1000000) (23751765897 / 250000) (2694537 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3820569 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3820569 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell982 :
    ∀ t ∈ Set.Icc ((50131 / 512000) : ℝ) (50163 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1216313081 / 1000000000) : ℝ) ≤ Real.exp (2 * (50131 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (50131 / 512000)) (1216313081 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((50163 / 512000) : ℝ)) ≤ (1216465131 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (50163 / 512000)) (1216465131 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((5946462583 / 62500) : ℝ) ≤ Real.exp (3 * (3821047 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3821047 / 1000000)) (5946462583 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((50131 / 512000) : ℝ) (50163 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3821047 / 1000000) (3821647 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (50131 / 512000) (50163 / 512000) (1216313081 / 1000000000) (1216465131 / 1000000000) (3821047 / 1000000) (3821647 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (50131 / 512000) (50163 / 512000) (3821047 / 1000000) (3821647 / 1000000) (35471 / 1000) (17747 / 500)
    (16369 / 250) (32917 / 500) (-142231 / 250) (301563 / 1000000) (341289 / 100) (672669 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3821047 / 1000000) (5946462583 / 62500) (672669 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3821047 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3821047 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell983 :
    ∀ t ∈ Set.Icc ((50163 / 512000) : ℝ) (10039 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((121646513 / 100000000) : ℝ) ≤ Real.exp (2 * (50163 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (50163 / 512000)) (121646513 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((10039 / 102400) : ℝ)) ≤ (608308599 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (10039 / 102400)) (608308599 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((23819983679 / 250000) : ℝ) ≤ Real.exp (3 * (152861 / 40000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (152861 / 40000)) (23819983679 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((50163 / 512000) : ℝ) (10039 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (152861 / 40000) (30577 / 8000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (50163 / 512000) (10039 / 102400) (121646513 / 100000000) (608308599 / 500000000) (152861 / 40000) (30577 / 8000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (50163 / 512000) (10039 / 102400) (152861 / 40000) (30577 / 8000) (35483 / 1000) (17753 / 500)
    (65541 / 1000) (65899 / 1000) (-71122 / 125) (301243 / 1000000) (1707299 / 500) (134341 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (152861 / 40000) (23819983679 / 250000) (134341 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (152861 / 40000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (152861 / 40000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell984 :
    ∀ t ∈ Set.Icc ((10039 / 102400) : ℝ) (50227 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1216617197 / 1000000000) : ℝ) ≤ Real.exp (2 * (10039 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (10039 / 102400)) (1216617197 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((50227 / 512000) : ℝ)) ≤ (243353857 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (50227 / 512000)) (243353857 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((95416377783 / 1000000) : ℝ) ≤ Real.exp (3 * (1911001 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1911001 / 500000)) (95416377783 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((10039 / 102400) : ℝ) (50227 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1911001 / 500000) (3822603 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (10039 / 102400) (50227 / 512000) (1216617197 / 1000000000) (243353857 / 200000000) (1911001 / 500000) (3822603 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (10039 / 102400) (50227 / 512000) (1911001 / 500000) (3822603 / 1000000) (7099 / 200) (17759 / 500)
    (32803 / 500) (13193 / 200) (-71128 / 125) (150463 / 500000) (3416307 / 1000) (1341489 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1911001 / 500000) (95416377783 / 1000000) (1341489 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1911001 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1911001 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell985 :
    ∀ t ∈ Set.Icc ((50227 / 512000) : ℝ) (50259 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((304192321 / 250000000) : ℝ) ≤ Real.exp (2 * (50227 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (50227 / 512000)) (304192321 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((50259 / 512000) : ℝ)) ≤ (1216921391 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (50259 / 512000)) (1216921391 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((95553302899 / 1000000) : ℝ) ≤ Real.exp (3 * (47781 / 12500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (47781 / 12500)) (95553302899 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((50227 / 512000) : ℝ) (50259 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (47781 / 12500) (3823081 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (50227 / 512000) (50259 / 512000) (304192321 / 250000000) (1216921391 / 1000000000) (47781 / 12500) (3823081 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (50227 / 512000) (50259 / 512000) (47781 / 12500) (3823081 / 1000000) (17753 / 500) (35529 / 1000)
    (65671 / 1000) (6603 / 100) (-142269 / 250) (300607 / 1000000) (427252 / 125) (2679133 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (47781 / 12500) (95553302899 / 1000000) (2679133 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (47781 / 12500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (47781 / 12500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell986 :
    ∀ t ∈ Set.Icc ((50259 / 512000) : ℝ) (50291 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((121692139 / 100000000) : ℝ) ≤ Real.exp (2 * (50259 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (50259 / 512000)) (121692139 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((50291 / 512000) : ℝ)) ≤ (243414703 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (50291 / 512000)) (243414703 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((95690424507 / 1000000) : ℝ) ≤ Real.exp (3 * (1911479 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1911479 / 500000)) (95690424507 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((50259 / 512000) : ℝ) (50291 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1911479 / 500000) (3823559 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (50259 / 512000) (50291 / 512000) (121692139 / 100000000) (243414703 / 200000000) (1911479 / 500000) (3823559 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (50259 / 512000) (50291 / 512000) (1911479 / 500000) (3823559 / 1000000) (17759 / 500) (35541 / 1000)
    (8217 / 125) (13219 / 200) (-71141 / 125) (300289 / 1000000) (136789 / 40) (1337647 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1911479 / 500000) (95690424507 / 1000000) (1337647 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1911479 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1911479 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell987 :
    ∀ t ∈ Set.Icc ((50291 / 512000) : ℝ) (50323 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((608536757 / 500000000) : ℝ) ≤ Real.exp (2 * (50291 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (50291 / 512000)) (608536757 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((50323 / 512000) : ℝ)) ≤ (1217225659 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (50323 / 512000)) (1217225659 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((95827742887 / 1000000) : ℝ) ≤ Real.exp (3 * (955859 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (955859 / 250000)) (95827742887 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((50291 / 512000) : ℝ) (50323 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (955859 / 250000) (3824037 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (50291 / 512000) (50323 / 512000) (608536757 / 500000000) (1217225659 / 1000000000) (955859 / 250000) (3824037 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (50291 / 512000) (50323 / 512000) (955859 / 250000) (3824037 / 1000000) (3553 / 100) (35553 / 1000)
    (65801 / 1000) (1654 / 25) (-28459 / 50) (299971 / 1000000) (855359 / 250) (2671461 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (955859 / 250000) (95827742887 / 1000000) (2671461 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (955859 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (955859 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell988 :
    ∀ t ∈ Set.Icc ((50323 / 512000) : ℝ) (10071 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((608612829 / 500000000) : ℝ) ≤ Real.exp (2 * (50323 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (50323 / 512000)) (608612829 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((10071 / 102400) : ℝ)) ≤ (608688911 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (10071 / 102400)) (608688911 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((47982629161 / 500000) : ℝ) ≤ Real.exp (3 * (1911957 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1911957 / 500000)) (47982629161 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((50323 / 512000) : ℝ) (10071 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1911957 / 500000) (764903 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (50323 / 512000) (10071 / 102400) (608612829 / 500000000) (608688911 / 500000000) (1911957 / 500000) (764903 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (50323 / 512000) (10071 / 102400) (1911957 / 500000) (764903 / 200000) (17771 / 500) (7113 / 200)
    (65867 / 1000) (33113 / 500) (-71154 / 125) (149827 / 500000) (3423147 / 1000) (2667633 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1911957 / 500000) (47982629161 / 500000) (2667633 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1911957 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1911957 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell989 :
    ∀ t ∈ Set.Icc ((10071 / 102400) : ℝ) (50387 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1217377821 / 1000000000) : ℝ) ≤ Real.exp (2 * (10071 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (10071 / 102400)) (1217377821 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((50387 / 512000) : ℝ)) ≤ (1217530003 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (50387 / 512000)) (1217530003 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((12012871387 / 125000) : ℝ) ≤ Real.exp (3 * (478049 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (478049 / 125000)) (12012871387 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((10071 / 102400) : ℝ) (50387 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (478049 / 125000) (3824993 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (10071 / 102400) (50387 / 512000) (1217377821 / 1000000000) (1217530003 / 1000000000) (478049 / 125000) (3824993 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (10071 / 102400) (50387 / 512000) (478049 / 125000) (3824993 / 1000000) (35553 / 1000) (4447 / 125)
    (16483 / 250) (66291 / 1000) (-569283 / 1000) (37417 / 125000) (1712429 / 500) (266381 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (478049 / 125000) (12012871387 / 125000) (266381 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (478049 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (478049 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell990 :
    ∀ t ∈ Set.Icc ((50387 / 512000) : ℝ) (50419 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((608765001 / 500000000) : ℝ) ≤ Real.exp (2 * (50387 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (50387 / 512000)) (608765001 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((50419 / 512000) : ℝ)) ≤ (304420551 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (50419 / 512000)) (304420551 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((96240881491 / 1000000) : ℝ) ≤ Real.exp (3 * (382487 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (382487 / 100000)) (96240881491 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((50387 / 512000) : ℝ) (50419 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (382487 / 100000) (3825471 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (50387 / 512000) (50419 / 512000) (608765001 / 500000000) (304420551 / 250000000) (382487 / 100000) (3825471 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (50387 / 512000) (50419 / 512000) (382487 / 100000) (3825471 / 1000000) (7113 / 200) (8897 / 250)
    (65997 / 1000) (16589 / 250) (-113867 / 200) (14951 / 50000) (3426571 / 1000) (2659993 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (382487 / 100000) (96240881491 / 1000000) (2659993 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (382487 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (382487 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell991 :
    ∀ t ∈ Set.Icc ((50419 / 512000) : ℝ) (50451 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1217682203 / 1000000000) : ℝ) ≤ Real.exp (2 * (50419 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (50419 / 512000)) (1217682203 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((50451 / 512000) : ℝ)) ≤ (152229303 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (50451 / 512000)) (152229303 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((96378989791 / 1000000) : ℝ) ≤ Real.exp (3 * (956337 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (956337 / 250000)) (96378989791 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((50419 / 512000) : ℝ) (50451 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (956337 / 250000) (3825949 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (50419 / 512000) (50451 / 512000) (1217682203 / 1000000000) (152229303 / 125000000) (956337 / 250000) (3825949 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (50419 / 512000) (50451 / 512000) (956337 / 250000) (3825949 / 1000000) (35577 / 1000) (178 / 5)
    (33031 / 500) (33211 / 500) (-284693 / 500) (298703 / 1000000) (857071 / 250) (2656181 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (956337 / 250000) (96378989791 / 1000000) (2656181 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (956337 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (956337 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell992 :
    ∀ t ∈ Set.Icc ((50451 / 512000) : ℝ) (50483 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1217834423 / 1000000000) : ℝ) ≤ Real.exp (2 * (50451 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (50451 / 512000)) (1217834423 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((50483 / 512000) : ℝ)) ≤ (1217986663 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (50483 / 512000)) (1217986663 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((96517296279 / 1000000) : ℝ) ≤ Real.exp (3 * (1912913 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1912913 / 500000)) (96517296279 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((50451 / 512000) : ℝ) (50483 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1912913 / 500000) (3826427 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (50451 / 512000) (50483 / 512000) (1217834423 / 1000000000) (1217986663 / 1000000000) (1912913 / 500000) (3826427 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (50451 / 512000) (50483 / 512000) (1912913 / 500000) (3826427 / 1000000) (35589 / 1000) (8903 / 250)
    (8266 / 125) (66487 / 1000) (-284719 / 500) (298387 / 1000000) (3429997 / 1000) (21219 / 8000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1912913 / 500000) (96517296279 / 1000000) (21219 / 8000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1912913 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1912913 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell993 :
    ∀ t ∈ Set.Icc ((50483 / 512000) : ℝ) (10103 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((608993331 / 500000000) : ℝ) ≤ Real.exp (2 * (50483 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (50483 / 512000)) (608993331 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((10103 / 102400) : ℝ)) ≤ (1218138921 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (10103 / 102400)) (1218138921 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((96656091209 / 1000000) : ℝ) ≤ Real.exp (3 * (765261 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (765261 / 200000)) (96656091209 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((50483 / 512000) : ℝ) (10103 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (765261 / 200000) (1913453 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (50483 / 512000) (10103 / 102400) (608993331 / 500000000) (1218138921 / 1000000000) (765261 / 200000) (1913453 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (50483 / 512000) (10103 / 102400) (765261 / 200000) (1913453 / 500000) (35601 / 1000) (4453 / 125)
    (66193 / 1000) (66553 / 1000) (-569489 / 1000) (29807 / 100000) (686343 / 200) (1324283 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (765261 / 200000) (96656091209 / 1000000) (1324283 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (765261 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (765261 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell994 :
    ∀ t ∈ Set.Icc ((10103 / 102400) : ℝ) (50547 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((30453473 / 25000000) : ℝ) ≤ Real.exp (2 * (10103 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (10103 / 102400)) (30453473 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((50547 / 512000) : ℝ)) ≤ (609145599 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (50547 / 512000)) (609145599 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((19358959069 / 200000) : ℝ) ≤ Real.exp (3 * (3826783 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3826783 / 1000000)) (19358959069 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((10103 / 102400) : ℝ) (50547 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3826783 / 1000000) (478423 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (10103 / 102400) (50547 / 512000) (30453473 / 25000000) (609145599 / 500000000) (3826783 / 1000000) (478423 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (10103 / 102400) (50547 / 512000) (3826783 / 1000000) (478423 / 125000) (8903 / 250) (7127 / 200)
    (66259 / 1000) (33309 / 500) (-28477 / 50) (59551 / 200000) (343343 / 100) (2644771 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3826783 / 1000000) (19358959069 / 200000) (2644771 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3826783 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3826783 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell995 :
    ∀ t ∈ Set.Icc ((50547 / 512000) : ℝ) (50579 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1218291197 / 1000000000) : ℝ) ≤ Real.exp (2 * (50547 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (50547 / 512000)) (1218291197 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((50579 / 512000) : ℝ)) ≤ (1218443493 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (50579 / 512000)) (1218443493 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3877347941 / 40000) : ℝ) ≤ Real.exp (3 * (3827261 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3827261 / 1000000)) (3877347941 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((50547 / 512000) : ℝ) (50579 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3827261 / 1000000) (3827863 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (50547 / 512000) (50579 / 512000) (1218291197 / 1000000000) (1218443493 / 1000000000) (3827261 / 1000000) (3827863 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (50547 / 512000) (50579 / 512000) (3827261 / 1000000) (3827863 / 1000000) (4453 / 125) (35647 / 1000)
    (16581 / 250) (16671 / 250) (-284793 / 500) (1859 / 6250) (3435149 / 1000) (2640981 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3827261 / 1000000) (3877347941 / 40000) (2640981 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3827261 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3827261 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell996 :
    ∀ t ∈ Set.Icc ((50579 / 512000) : ℝ) (50611 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((304610873 / 250000000) : ℝ) ≤ Real.exp (2 * (50579 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (50579 / 512000)) (304610873 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((50611 / 512000) : ℝ)) ≤ (38081119 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (50611 / 512000)) (38081119 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((48536546127 / 500000) : ℝ) ≤ Real.exp (3 * (191387 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (191387 / 50000)) (48536546127 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((50579 / 512000) : ℝ) (50611 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (191387 / 50000) (3828341 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (50579 / 512000) (50611 / 512000) (304610873 / 250000000) (38081119 / 31250000) (191387 / 50000) (3828341 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (50579 / 512000) (50611 / 512000) (191387 / 50000) (3828341 / 1000000) (8909 / 250) (35659 / 1000)
    (6639 / 100) (66749 / 1000) (-284821 / 500) (74281 / 250000) (687373 / 200) (2637189 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (191387 / 50000) (48536546127 / 500000) (2637189 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (191387 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (191387 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell997 :
    ∀ t ∈ Set.Icc ((50611 / 512000) : ℝ) (50643 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1218595807 / 1000000000) : ℝ) ≤ Real.exp (2 * (50611 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (50611 / 512000)) (1218595807 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((50643 / 512000) : ℝ)) ≤ (609374071 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (50643 / 512000)) (609374071 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((97212394797 / 1000000) : ℝ) ≤ Real.exp (3 * (1914109 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1914109 / 500000)) (97212394797 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((50611 / 512000) : ℝ) (50643 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1914109 / 500000) (191441 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (50611 / 512000) (50643 / 512000) (1218595807 / 1000000000) (609374071 / 500000000) (1914109 / 500000) (191441 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (50611 / 512000) (50643 / 512000) (1914109 / 500000) (191441 / 50000) (4456 / 125) (35671 / 1000)
    (13291 / 200) (13363 / 200) (-71211 / 125) (296809 / 1000000) (1719293 / 500) (263341 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1914109 / 500000) (97212394797 / 1000000) (263341 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1914109 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1914109 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell998 :
    ∀ t ∈ Set.Icc ((50643 / 512000) : ℝ) (2027 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1218748141 / 1000000000) : ℝ) ≤ Real.exp (2 * (50643 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (50643 / 512000)) (1218748141 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2027 / 20480) : ℝ)) ≤ (243780099 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2027 / 20480)) (243780099 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((48676094649 / 500000) : ℝ) ≤ Real.exp (3 * (3828697 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3828697 / 1000000)) (48676094649 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((50643 / 512000) : ℝ) (2027 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3828697 / 1000000) (1914649 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (50643 / 512000) (2027 / 20480) (1218748141 / 1000000000) (243780099 / 200000000) (3828697 / 1000000) (1914649 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (50643 / 512000) (2027 / 20480) (3828697 / 1000000) (1914649 / 500000) (35659 / 1000) (17841 / 500)
    (66521 / 1000) (1672 / 25) (-569743 / 1000) (148247 / 500000) (3440303 / 1000) (657407 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3828697 / 1000000) (48676094649 / 500000) (657407 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3828697 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3828697 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell999 :
    ∀ t ∈ Set.Icc ((2027 / 20480) : ℝ) (50707 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((609450247 / 500000000) : ℝ) ≤ Real.exp (2 * (2027 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2027 / 20480)) (609450247 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((50707 / 512000) : ℝ)) ≤ (304763217 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (50707 / 512000)) (304763217 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((97491892353 / 1000000) : ℝ) ≤ Real.exp (3 * (153167 / 40000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (153167 / 40000)) (97491892353 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2027 / 20480) : ℝ) (50707 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (153167 / 40000) (3829777 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2027 / 20480) (50707 / 512000) (609450247 / 500000000) (304763217 / 250000000) (153167 / 40000) (3829777 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2027 / 20480) (50707 / 512000) (153167 / 40000) (3829777 / 1000000) (35671 / 1000) (17847 / 500)
    (33293 / 500) (33473 / 500) (-569789 / 1000) (296181 / 1000000) (137681 / 40) (131293 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (153167 / 40000) (97491892353 / 1000000) (131293 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (153167 / 40000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (153167 / 40000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch049 :
    ∀ t ∈ Set.Icc ((50067 / 512000) : ℝ) (50707 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell980
      hpThetaDensityLowerExpCompact_cell981)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell982
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell983
      hpThetaDensityLowerExpCompact_cell984)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell985
      hpThetaDensityLowerExpCompact_cell986)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell987
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell988
      hpThetaDensityLowerExpCompact_cell989))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell990
      hpThetaDensityLowerExpCompact_cell991)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell992
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell993
      hpThetaDensityLowerExpCompact_cell994)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell995
      hpThetaDensityLowerExpCompact_cell996)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell997
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell998
      hpThetaDensityLowerExpCompact_cell999)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch049
end HodgeProofHP
