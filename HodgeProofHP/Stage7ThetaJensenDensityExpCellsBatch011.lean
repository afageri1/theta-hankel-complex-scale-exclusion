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
theorem hpThetaDensityExpCompact_cell220 :
    ∀ t ∈ Set.Icc ((421 / 3200) : ℝ) (2109 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((325247333 / 250000000) : ℝ) ≤ Real.exp (2 * (421 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (421 / 3200)) (325247333 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2109 / 16000) : ℝ)) ≤ (130163999 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2109 / 16000)) (130163999 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((21132849923 / 100000) : ℝ) ≤ Real.exp (3 * (4087057 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4087057 / 1000000)) (21132849923 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((421 / 3200) : ℝ) (2109 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4087057 / 1000000) (4089233 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (421 / 3200) (2109 / 16000) (325247333 / 250000000) (130163999 / 100000000) (4087057 / 1000000) (4089233 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (421 / 3200) (2109 / 16000) (4087057 / 1000000) (4089233 / 1000000) (1057 / 25) (8473 / 200)
    (105813 / 1000) (53627 / 500) (-566529 / 1000) (166331 / 1000000) (559239 / 125) (242277 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4087057 / 1000000) (21132849923 / 100000) (242277 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4087057 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4087057 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell221 :
    ∀ t ∈ Set.Icc ((2109 / 16000) : ℝ) (2113 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1301639989 / 1000000000) : ℝ) ≤ Real.exp (2 * (2109 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2109 / 16000)) (1301639989 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2113 / 16000) : ℝ)) ≤ (1302290973 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2113 / 16000)) (1302290973 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((42525796109 / 200000) : ℝ) ≤ Real.exp (3 * (2044551 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2044551 / 500000)) (42525796109 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2109 / 16000) : ℝ) (2113 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2044551 / 500000) (2045639 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2109 / 16000) (2113 / 16000) (1301639989 / 1000000000) (1302290973 / 1000000000) (2044551 / 500000) (2045639 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2109 / 16000) (2113 / 16000) (2044551 / 500000) (2045639 / 500000) (8467 / 200) (2121 / 50)
    (53081 / 500) (26901 / 250) (-566373 / 1000) (82781 / 500000) (1120717 / 250) (150497 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2044551 / 500000) (42525796109 / 200000) (150497 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2044551 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2044551 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell222 :
    ∀ t ∈ Set.Icc ((2113 / 16000) : ℝ) (2117 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((325572743 / 250000000) : ℝ) ≤ Real.exp (2 * (2113 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2113 / 16000)) (325572743 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2117 / 16000) : ℝ)) ≤ (1302942281 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2117 / 16000)) (1302942281 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((53484366193 / 250000) : ℝ) ≤ Real.exp (3 * (4091147 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4091147 / 1000000)) (53484366193 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2113 / 16000) : ℝ) (2117 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4091147 / 1000000) (1023331 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2113 / 16000) (2117 / 16000) (325572743 / 250000000) (1302942281 / 1000000000) (4091147 / 1000000) (1023331 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2113 / 16000) (2117 / 16000) (4091147 / 1000000) (1023331 / 250000) (42389 / 1000) (1699 / 40)
    (13314 / 125) (21591 / 200) (-70776 / 125) (41199 / 250000) (2245921 / 500) (299153 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4091147 / 1000000) (53484366193 / 250000) (299153 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4091147 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4091147 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell223 :
    ∀ t ∈ Set.Icc ((2117 / 16000) : ℝ) (2121 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((32573557 / 25000000) : ℝ) ≤ Real.exp (2 * (2117 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2117 / 16000)) (32573557 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2121 / 16000) : ℝ)) ≤ (260718783 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2121 / 16000)) (260718783 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((215254646919 / 1000000) : ℝ) ≤ Real.exp (3 * (4093193 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4093193 / 1000000)) (215254646919 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2117 / 16000) : ℝ) (2121 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4093193 / 1000000) (4095371 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2117 / 16000) (2121 / 16000) (32573557 / 25000000) (260718783 / 200000000) (4093193 / 1000000) (4095371 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2117 / 16000) (2121 / 16000) (4093193 / 1000000) (4095371 / 1000000) (10611 / 250) (4253 / 100)
    (53431 / 500) (108307 / 1000) (-566039 / 1000) (164033 / 1000000) (2250417 / 500) (118929 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4093193 / 1000000) (215254646919 / 1000000) (118929 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4093193 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4093193 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell224 :
    ∀ t ∈ Set.Icc ((2121 / 16000) : ℝ) (17 / 128), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((651796957 / 500000000) : ℝ) ≤ Real.exp (2 * (2121 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2121 / 16000)) (651796957 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((17 / 128) : ℝ)) ≤ (10433967 / 8000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (17 / 128)) (10433967 / 8000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13536286779 / 62500) : ℝ) ≤ Real.exp (3 * (102381 / 25000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (102381 / 25000)) (13536286779 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2121 / 16000) : ℝ) (17 / 128),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (102381 / 25000) (4097419 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2121 / 16000) (17 / 128) (651796957 / 500000000) (10433967 / 8000000) (102381 / 25000) (4097419 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2121 / 16000) (17 / 128) (102381 / 25000) (4097419 / 1000000) (42499 / 1000) (5323 / 125)
    (107213 / 1000) (108659 / 1000) (-282933 / 500) (81637 / 500000) (1127461 / 250) (1182009 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (102381 / 25000) (13536286779 / 62500) (1182009 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (102381 / 25000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (102381 / 25000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell225 :
    ∀ t ∈ Set.Icc ((17 / 128) : ℝ) (2129 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((652122937 / 500000000) : ℝ) ≤ Real.exp (2 * (17 / 128)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (17 / 128)) (652122937 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2129 / 16000) : ℝ)) ≤ (1304898161 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2129 / 16000)) (1304898161 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13619709459 / 62500) : ℝ) ≤ Real.exp (3 * (512161 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (512161 / 125000)) (13619709459 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((17 / 128) : ℝ) (2129 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (512161 / 125000) (4099469 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (17 / 128) (2129 / 16000) (652122937 / 500000000) (1304898161 / 1000000000) (512161 / 125000) (4099469 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (17 / 128) (2129 / 16000) (512161 / 125000) (4099469 / 1000000) (21277 / 500) (42639 / 1000)
    (26891 / 250) (109013 / 1000) (-113137 / 200) (81259 / 500000) (1129719 / 250) (1174769 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (512161 / 125000) (13619709459 / 62500) (1174769 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (512161 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (512161 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell226 :
    ∀ t ∈ Set.Icc ((2129 / 16000) : ℝ) (2133 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((16311227 / 12500000) : ℝ) ≤ Real.exp (2 * (2129 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2129 / 16000)) (16311227 / 12500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2133 / 16000) : ℝ)) ≤ (1305550773 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2133 / 16000)) (1305550773 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((43851799591 / 200000) : ℝ) ≤ Real.exp (3 * (4099337 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4099337 / 1000000)) (43851799591 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2129 / 16000) : ℝ) (2133 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4099337 / 1000000) (4101519 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2129 / 16000) (2133 / 16000) (16311227 / 12500000) (1305550773 / 1000000000) (4099337 / 1000000) (4101519 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2129 / 16000) (2133 / 16000) (4099337 / 1000000) (4101519 / 1000000) (42609 / 1000) (21347 / 500)
    (26979 / 250) (109367 / 1000) (-113101 / 200) (40441 / 250000) (2263961 / 500) (1167569 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4099337 / 1000000) (43851799591 / 200000) (1167569 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4099337 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4099337 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell227 :
    ∀ t ∈ Set.Icc ((2133 / 16000) : ℝ) (2137 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((326387693 / 250000000) : ℝ) ≤ Real.exp (2 * (2133 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2133 / 16000)) (326387693 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2137 / 16000) : ℝ)) ≤ (20409433 / 15625000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2137 / 16000)) (20409433 / 15625000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((5515289779 / 25000) : ℝ) ≤ Real.exp (3 * (4101387 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4101387 / 1000000)) (5515289779 / 25000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2133 / 16000) : ℝ) (2137 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4101387 / 1000000) (410357 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2133 / 16000) (2137 / 16000) (326387693 / 250000000) (20409433 / 15625000) (4101387 / 1000000) (410357 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2133 / 16000) (2137 / 16000) (4101387 / 1000000) (410357 / 100000) (5333 / 125) (42749 / 1000)
    (108269 / 1000) (54861 / 500) (-565323 / 1000) (80507 / 500000) (2268493 / 500) (1160411 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4101387 / 1000000) (5515289779 / 25000) (1160411 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4101387 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4101387 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell228 :
    ∀ t ∈ Set.Icc ((2137 / 16000) : ℝ) (2141 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1306203711 / 1000000000) : ℝ) ≤ Real.exp (2 * (2137 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2137 / 16000)) (1306203711 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2141 / 16000) : ℝ)) ≤ (1306856977 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2141 / 16000)) (1306856977 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((22197319429 / 100000) : ℝ) ≤ Real.exp (3 * (2051719 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2051719 / 500000)) (22197319429 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2137 / 16000) : ℝ) (2141 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2051719 / 500000) (2052811 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2137 / 16000) (2141 / 16000) (1306203711 / 1000000000) (1306856977 / 1000000000) (2051719 / 500000) (2052811 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2137 / 16000) (2141 / 16000) (2051719 / 500000) (2052811 / 500000) (42719 / 1000) (10701 / 250)
    (108623 / 1000) (55039 / 500) (-70642 / 125) (80133 / 500000) (4546067 / 1000) (1153293 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2051719 / 500000) (22197319429 / 100000) (1153293 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2051719 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2051719 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell229 :
    ∀ t ∈ Set.Icc ((2141 / 16000) : ℝ) (429 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((81678561 / 62500000) : ℝ) ≤ Real.exp (2 * (2141 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2141 / 16000)) (81678561 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((429 / 3200) : ℝ)) ≤ (1307510569 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (429 / 3200)) (1307510569 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((223344541177 / 1000000) : ℝ) ≤ Real.exp (3 * (4105491 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4105491 / 1000000)) (223344541177 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2141 / 16000) : ℝ) (429 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4105491 / 1000000) (1026919 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2141 / 16000) (429 / 3200) (81678561 / 62500000) (1307510569 / 1000000000) (4105491 / 1000000) (1026919 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2141 / 16000) (429 / 3200) (4105491 / 1000000) (1026919 / 250000) (21387 / 500) (2143 / 50)
    (54489 / 500) (22087 / 200) (-282473 / 500) (159521 / 1000000) (1138793 / 250) (286553 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4105491 / 1000000) (223344541177 / 1000000) (286553 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4105491 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4105491 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell230 :
    ∀ t ∈ Set.Icc ((429 / 3200) : ℝ) (2149 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((163438821 / 125000000) : ℝ) ≤ Real.exp (2 * (429 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (429 / 3200)) (163438821 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2149 / 16000) : ℝ)) ≤ (163520561 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2149 / 16000)) (163520561 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((112362180089 / 500000) : ℝ) ≤ Real.exp (3 * (513443 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (513443 / 125000)) (112362180089 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((429 / 3200) : ℝ) (2149 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (513443 / 125000) (410973 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (429 / 3200) (2149 / 16000) (163438821 / 125000000) (163520561 / 125000000) (513443 / 125000) (410973 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (429 / 3200) (2149 / 16000) (513443 / 125000) (410973 / 100000) (42829 / 1000) (8583 / 200)
    (109333 / 1000) (13849 / 125) (-564753 / 1000) (7939 / 50000) (456429 / 100) (569587 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (513443 / 125000) (112362180089 / 500000) (569587 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (513443 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (513443 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell231 :
    ∀ t ∈ Set.Icc ((2149 / 16000) : ℝ) (2153 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1308164487 / 1000000000) : ℝ) ≤ Real.exp (2 * (2149 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2149 / 16000)) (1308164487 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2153 / 16000) : ℝ)) ≤ (654409367 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2153 / 16000)) (654409367 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((22611338197 / 100000) : ℝ) ≤ Real.exp (3 * (2054799 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2054799 / 500000)) (22611338197 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2149 / 16000) : ℝ) (2153 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2054799 / 500000) (822357 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2149 / 16000) (2153 / 16000) (1308164487 / 1000000000) (654409367 / 500000000) (2054799 / 500000) (822357 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2149 / 16000) (2153 / 16000) (2054799 / 500000) (822357 / 200000) (10721 / 250) (4297 / 100)
    (109689 / 1000) (2223 / 20) (-141139 / 250) (158041 / 1000000) (2286713 / 500) (70761 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2054799 / 500000) (22611338197 / 100000) (70761 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2054799 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2054799 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell232 :
    ∀ t ∈ Set.Icc ((2153 / 16000) : ℝ) (2157 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1308818733 / 1000000000) : ℝ) ≤ Real.exp (2 * (2153 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2153 / 16000)) (1308818733 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2157 / 16000) : ℝ)) ≤ (1309473307 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2157 / 16000)) (1309473307 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((28439044291 / 125000) : ℝ) ≤ Real.exp (3 * (2055827 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2055827 / 500000)) (28439044291 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2153 / 16000) : ℝ) (2157 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2055827 / 500000) (2056921 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2153 / 16000) (2157 / 16000) (1308818733 / 1000000000) (1309473307 / 1000000000) (2055827 / 500000) (2056921 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2153 / 16000) (2157 / 16000) (2055827 / 500000) (2056921 / 500000) (42939 / 1000) (1721 / 40)
    (55023 / 500) (27877 / 250) (-141089 / 250) (31461 / 200000) (572823 / 125) (562607 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2055827 / 500000) (28439044291 / 125000) (562607 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2055827 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2055827 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell233 :
    ∀ t ∈ Set.Icc ((2157 / 16000) : ℝ) (2161 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((654736653 / 500000000) : ℝ) ≤ Real.exp (2 * (2157 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2157 / 16000)) (654736653 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2161 / 16000) : ℝ)) ≤ (1310128207 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2161 / 16000)) (1310128207 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((45783996427 / 200000) : ℝ) ≤ Real.exp (3 * (411371 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (411371 / 100000)) (45783996427 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2157 / 16000) : ℝ) (2161 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (411371 / 100000) (4115899 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2157 / 16000) (2161 / 16000) (654736653 / 500000000) (1310128207 / 1000000000) (411371 / 100000) (4115899 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2157 / 16000) (2161 / 16000) (411371 / 100000) (4115899 / 1000000) (8599 / 200) (43081 / 1000)
    (27601 / 250) (27967 / 250) (-70519 / 125) (156573 / 1000000) (4591757 / 1000) (223659 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (411371 / 100000) (45783996427 / 200000) (223659 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (411371 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (411371 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell234 :
    ∀ t ∈ Set.Icc ((2161 / 16000) : ℝ) (433 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((655064103 / 500000000) : ℝ) ≤ Real.exp (2 * (2161 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2161 / 16000)) (655064103 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((433 / 3200) : ℝ)) ≤ (262156687 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (433 / 3200)) (262156687 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((230337009951 / 1000000) : ℝ) ≤ Real.exp (3 * (4115767 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4115767 / 1000000)) (230337009951 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2161 / 16000) : ℝ) (433 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4115767 / 1000000) (2058979 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2161 / 16000) (433 / 3200) (655064103 / 500000000) (262156687 / 200000000) (4115767 / 1000000) (2058979 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2161 / 16000) (433 / 3200) (4115767 / 1000000) (2058979 / 500000) (861 / 20) (5392 / 125)
    (55381 / 500) (28057 / 250) (-563939 / 1000) (155843 / 1000000) (575119 / 125) (222283 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4115767 / 1000000) (230337009951 / 1000000) (222283 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4115767 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4115767 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell235 :
    ∀ t ∈ Set.Icc ((433 / 3200) : ℝ) (2169 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((655391717 / 500000000) : ℝ) ≤ Real.exp (2 * (433 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (433 / 3200)) (655391717 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2169 / 16000) : ℝ)) ≤ (1311438991 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2169 / 16000)) (1311438991 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((231764199777 / 1000000) : ℝ) ≤ Real.exp (3 * (2058913 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2058913 / 500000)) (231764199777 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((433 / 3200) : ℝ) (2169 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2058913 / 500000) (4120017 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (433 / 3200) (2169 / 16000) (655391717 / 500000000) (1311438991 / 1000000000) (2058913 / 500000) (4120017 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (433 / 3200) (2169 / 16000) (2058913 / 500000) (4120017 / 1000000) (8621 / 200) (5399 / 125)
    (55561 / 500) (112589 / 1000) (-563733 / 1000) (38779 / 250000) (4610161 / 1000) (1104571 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2058913 / 500000) (231764199777 / 1000000) (1104571 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2058913 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2058913 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell236 :
    ∀ t ∈ Set.Icc ((2169 / 16000) : ℝ) (2173 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((131143899 / 100000000) : ℝ) ≤ Real.exp (2 * (2169 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2169 / 16000)) (131143899 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2173 / 16000) : ℝ)) ≤ (656047437 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2173 / 16000)) (656047437 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((58300058139 / 250000) : ℝ) ≤ Real.exp (3 * (823977 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (823977 / 200000)) (58300058139 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2169 / 16000) : ℝ) (2173 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (823977 / 200000) (2061039 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2169 / 16000) (2173 / 16000) (131143899 / 100000000) (656047437 / 500000000) (823977 / 200000) (2061039 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2169 / 16000) (2173 / 16000) (823977 / 200000) (2061039 / 500000) (43161 / 1000) (43247 / 1000)
    (111481 / 1000) (112951 / 1000) (-563513 / 1000) (19299 / 125000) (577424 / 125) (109777 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (823977 / 200000) (58300058139 / 250000) (109777 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (823977 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (823977 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell237 :
    ∀ t ∈ Set.Icc ((2173 / 16000) : ℝ) (2177 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1312094873 / 1000000000) : ℝ) ≤ Real.exp (2 * (2173 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2173 / 16000)) (1312094873 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2177 / 16000) : ℝ)) ≤ (262550217 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2177 / 16000)) (262550217 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4692931419 / 20000) : ℝ) ≤ Real.exp (3 * (2060973 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2060973 / 500000)) (4692931419 / 20000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2173 / 16000) : ℝ) (2177 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2060973 / 500000) (4124139 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2173 / 16000) (2177 / 16000) (1312094873 / 1000000000) (262550217 / 200000000) (2060973 / 500000) (4124139 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2173 / 16000) (2177 / 16000) (2060973 / 500000) (4124139 / 1000000) (5402 / 125) (43303 / 1000)
    (55921 / 500) (56657 / 500) (-5633 / 10) (153671 / 1000000) (2314319 / 500) (1091003 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2060973 / 500000) (4692931419 / 20000) (1091003 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2060973 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2060973 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell238 :
    ∀ t ∈ Set.Icc ((2177 / 16000) : ℝ) (2181 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((328187771 / 250000000) : ℝ) ≤ Real.exp (2 * (2177 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2177 / 16000)) (328187771 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2181 / 16000) : ℝ)) ≤ (10507261 / 8000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2181 / 16000)) (10507261 / 8000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((29512734959 / 125000) : ℝ) ≤ Real.exp (3 * (4124007 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4124007 / 1000000)) (29512734959 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2177 / 16000) : ℝ) (2181 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4124007 / 1000000) (2063101 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2177 / 16000) (2181 / 16000) (328187771 / 250000000) (10507261 / 8000000) (4124007 / 1000000) (2063101 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2177 / 16000) (2181 / 16000) (4124007 / 1000000) (2063101 / 500000) (5409 / 125) (43359 / 1000)
    (28051 / 250) (113677 / 1000) (-70384 / 125) (152953 / 1000000) (2318953 / 500) (542139 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4124007 / 1000000) (29512734959 / 125000) (542139 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4124007 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4124007 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell239 :
    ∀ t ∈ Set.Icc ((2181 / 16000) : ℝ) (437 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((164175953 / 125000000) : ℝ) ≤ Real.exp (2 * (2181 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2181 / 16000)) (164175953 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((437 / 3200) : ℝ)) ≤ (1314064493 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (437 / 3200)) (1314064493 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((118783819877 / 500000) : ℝ) ≤ Real.exp (3 * (412607 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (412607 / 100000)) (118783819877 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2181 / 16000) : ℝ) (437 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (412607 / 100000) (2064133 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2181 / 16000) (437 / 3200) (164175953 / 125000000) (1314064493 / 1000000000) (412607 / 100000) (2064133 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2181 / 16000) (437 / 3200) (412607 / 100000) (2064133 / 500000) (5416 / 125) (21707 / 500)
    (56283 / 500) (114041 / 1000) (-562847 / 1000) (152237 / 1000000) (4647193 / 1000) (269397 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (412607 / 100000) (118783819877 / 500000) (269397 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (412607 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (412607 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityExpCompact_cellsBatch011 :
    ∀ t ∈ Set.Icc ((421 / 3200) : ℝ) (437 / 3200),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell220
      hpThetaDensityExpCompact_cell221)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell222
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell223
      hpThetaDensityExpCompact_cell224)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell225
      hpThetaDensityExpCompact_cell226)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell227
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell228
      hpThetaDensityExpCompact_cell229))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell230
      hpThetaDensityExpCompact_cell231)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell232
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell233
      hpThetaDensityExpCompact_cell234)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell235
      hpThetaDensityExpCompact_cell236)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell237
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell238
      hpThetaDensityExpCompact_cell239)))))

#print axioms hpThetaDensityExpCompact_cellsBatch011
end HodgeProofHP
