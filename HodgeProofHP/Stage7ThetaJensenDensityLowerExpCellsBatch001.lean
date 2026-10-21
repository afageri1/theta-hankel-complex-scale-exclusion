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
theorem hpThetaDensityLowerExpCompact_cell020 :
    ∀ t ∈ Set.Icc ((2049 / 25600) : ℝ) (40981 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((234720511 / 200000000) : ℝ) ≤ Real.exp (2 * (2049 / 25600)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2049 / 25600)) (234720511 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((40981 / 512000) : ℝ)) ≤ (58680357 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (40981 / 512000)) (58680357 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63615712797 / 1000000) : ℝ) ≤ Real.exp (3 * (460859 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (460859 / 125000)) (63615712797 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2049 / 25600) : ℝ) (40981 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (460859 / 125000) (737401 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2049 / 25600) (40981 / 512000) (234720511 / 200000000) (58680357 / 50000000) (460859 / 125000) (737401 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2049 / 25600) (40981 / 512000) (460859 / 125000) (737401 / 200000) (129 / 4) (6451 / 200)
    (6051 / 125) (12121 / 250) (-275729 / 500) (202503 / 500000) (369594 / 125) (1006041 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (460859 / 125000) (63615712797 / 1000000) (1006041 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (460859 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (460859 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell021 :
    ∀ t ∈ Set.Icc ((40981 / 512000) : ℝ) (20491 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173607139 / 1000000000) : ℝ) ≤ Real.exp (2 * (40981 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (40981 / 512000)) (1173607139 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20491 / 256000) : ℝ)) ≤ (293402931 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20491 / 256000)) (293402931 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63618384711 / 1000000) : ℝ) ≤ Real.exp (3 * (1843443 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1843443 / 500000)) (63618384711 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((40981 / 512000) : ℝ) (20491 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1843443 / 500000) (3687019 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (40981 / 512000) (20491 / 256000) (1173607139 / 1000000000) (293402931 / 250000000) (1843443 / 500000) (3687019 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (40981 / 512000) (20491 / 256000) (1843443 / 500000) (3687019 / 1000000) (129 / 4) (4032 / 125)
    (4841 / 100) (24243 / 500) (-27573 / 50) (404993 / 1000000) (2956797 / 1000) (804799 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1843443 / 500000) (63618384711 / 1000000) (804799 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843443 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843443 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell022 :
    ∀ t ∈ Set.Icc ((20491 / 256000) : ℝ) (40983 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173611723 / 1000000000) : ℝ) ≤ Real.exp (2 * (20491 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20491 / 256000)) (1173611723 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((40983 / 512000) : ℝ)) ≤ (1173616309 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (40983 / 512000)) (1173616309 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31810623801 / 500000) : ℝ) ≤ Real.exp (3 * (3686901 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3686901 / 1000000)) (31810623801 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20491 / 256000) : ℝ) (40983 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3686901 / 1000000) (3687033 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20491 / 256000) (40983 / 512000) (1173611723 / 1000000000) (1173616309 / 1000000000) (3686901 / 1000000) (3687033 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20491 / 256000) (40983 / 512000) (3686901 / 1000000) (3687033 / 1000000) (129 / 4) (4032 / 125)
    (12103 / 250) (48487 / 1000) (-551467 / 1000) (20249 / 50000) (1478421 / 500) (4023813 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3686901 / 1000000) (31810623801 / 500000) (4023813 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3686901 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3686901 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell023 :
    ∀ t ∈ Set.Icc ((40983 / 512000) : ℝ) (5123 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293404077 / 250000000) : ℝ) ≤ Real.exp (2 * (40983 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (40983 / 512000)) (293404077 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((5123 / 64000) : ℝ)) ≤ (1173620893 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (5123 / 64000)) (1173620893 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63623919749 / 1000000) : ℝ) ≤ Real.exp (3 * (737383 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (737383 / 200000)) (63623919749 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((40983 / 512000) : ℝ) (5123 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (737383 / 200000) (460881 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (40983 / 512000) (5123 / 64000) (293404077 / 250000000) (1173620893 / 1000000000) (737383 / 200000) (460881 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (40983 / 512000) (5123 / 64000) (737383 / 200000) (460881 / 125000) (32251 / 1000) (4032 / 125)
    (24207 / 500) (48489 / 1000) (-110293 / 200) (404967 / 1000000) (295689 / 100) (1005911 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (737383 / 200000) (63623919749 / 1000000) (1005911 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (737383 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (737383 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell024 :
    ∀ t ∈ Set.Icc ((5123 / 64000) : ℝ) (8197 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293405223 / 250000000) : ℝ) ≤ Real.exp (2 * (5123 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (5123 / 64000)) (293405223 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8197 / 102400) : ℝ)) ≤ (586812739 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8197 / 102400)) (586812739 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63626782889 / 1000000) : ℝ) ≤ Real.exp (3 * (368693 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (368693 / 100000)) (63626782889 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((5123 / 64000) : ℝ) (8197 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (368693 / 100000) (1843531 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (5123 / 64000) (8197 / 102400) (293405223 / 250000000) (586812739 / 500000000) (368693 / 100000) (1843531 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (5123 / 64000) (8197 / 102400) (368693 / 100000) (1843531 / 500000) (32251 / 1000) (32257 / 1000)
    (6052 / 125) (48491 / 1000) (-68934 / 125) (202477 / 500000) (591387 / 200) (4023463 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (368693 / 100000) (63626782889 / 1000000) (4023463 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (368693 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (368693 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell025 :
    ∀ t ∈ Set.Icc ((8197 / 102400) : ℝ) (20493 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173625477 / 1000000000) : ℝ) ≤ Real.exp (2 * (8197 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8197 / 102400)) (1173625477 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20493 / 256000) : ℝ)) ≤ (586815031 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20493 / 256000)) (586815031 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63629455269 / 1000000) : ℝ) ≤ Real.exp (3 * (115217 / 31250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (115217 / 31250)) (63629455269 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8197 / 102400) : ℝ) (20493 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (115217 / 31250) (3687077 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8197 / 102400) (20493 / 256000) (1173625477 / 1000000000) (586815031 / 500000000) (115217 / 31250) (3687077 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8197 / 102400) (20493 / 256000) (115217 / 31250) (3687077 / 1000000) (32251 / 1000) (32257 / 1000)
    (48417 / 1000) (48493 / 1000) (-551471 / 1000) (202471 / 500000) (2956983 / 1000) (2011647 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (115217 / 31250) (63629455269 / 1000000) (2011647 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (115217 / 31250)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (115217 / 31250)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell026 :
    ∀ t ∈ Set.Icc ((20493 / 256000) : ℝ) (40987 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173630061 / 1000000000) : ℝ) ≤ Real.exp (2 * (20493 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20493 / 256000)) (1173630061 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((40987 / 512000) : ℝ)) ≤ (1173634647 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (40987 / 512000)) (1173634647 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63632127761 / 1000000) : ℝ) ≤ Real.exp (3 * (1843479 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1843479 / 500000)) (63632127761 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20493 / 256000) : ℝ) (40987 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1843479 / 500000) (3687091 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20493 / 256000) (40987 / 512000) (1173630061 / 1000000000) (1173634647 / 1000000000) (1843479 / 500000) (3687091 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20493 / 256000) (40987 / 512000) (1843479 / 500000) (3687091 / 1000000) (8063 / 250) (32257 / 1000)
    (48419 / 1000) (24247 / 500) (-551473 / 1000) (404929 / 1000000) (739257 / 250) (6437 / 1600000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1843479 / 500000) (63632127761 / 1000000) (6437 / 1600000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843479 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843479 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell027 :
    ∀ t ∈ Set.Icc ((40987 / 512000) : ℝ) (10247 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((586817323 / 500000000) : ℝ) ≤ Real.exp (2 * (40987 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (40987 / 512000)) (586817323 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((10247 / 128000) : ℝ)) ≤ (1173639231 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (10247 / 128000)) (1173639231 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6363499127 / 100000) : ℝ) ≤ Real.exp (3 * (3686973 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3686973 / 1000000)) (6363499127 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((40987 / 512000) : ℝ) (10247 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3686973 / 1000000) (1843553 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (40987 / 512000) (10247 / 128000) (586817323 / 500000000) (1173639231 / 1000000000) (3686973 / 1000000) (1843553 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (40987 / 512000) (10247 / 128000) (3686973 / 1000000) (1843553 / 500000) (8063 / 250) (16129 / 500)
    (2421 / 50) (6062 / 125) (-137869 / 250) (101229 / 250000) (739269 / 250) (125717 / 31250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3686973 / 1000000) (6363499127 / 100000) (125717 / 31250000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3686973 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3686973 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell028 :
    ∀ t ∈ Set.Icc ((10247 / 128000) : ℝ) (40989 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((117363923 / 100000000) : ℝ) ≤ Real.exp (2 * (10247 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (10247 / 128000)) (117363923 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((40989 / 512000) : ℝ)) ≤ (146705477 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (40989 / 512000)) (146705477 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31818831997 / 500000) : ℝ) ≤ Real.exp (3 * (3686987 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3686987 / 1000000)) (31818831997 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((10247 / 128000) : ℝ) (40989 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3686987 / 1000000) (46089 / 12500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (10247 / 128000) (40989 / 512000) (117363923 / 100000000) (146705477 / 125000000) (3686987 / 1000000) (46089 / 12500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (10247 / 128000) (40989 / 512000) (3686987 / 1000000) (46089 / 12500) (8063 / 250) (16129 / 500)
    (24211 / 500) (24249 / 500) (-275739 / 500) (50613 / 125000) (2957121 / 1000) (160911 / 40000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3686987 / 1000000) (31818831997 / 500000) (160911 / 40000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3686987 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3686987 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell029 :
    ∀ t ∈ Set.Icc ((40989 / 512000) : ℝ) (4099 / 51200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((234728763 / 200000000) : ℝ) ≤ Real.exp (2 * (40989 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (40989 / 512000)) (234728763 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4099 / 51200) : ℝ)) ≤ (2934121 / 2500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4099 / 51200)) (2934121 / 2500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((7955065969 / 125000) : ℝ) ≤ Real.exp (3 * (1843501 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1843501 / 500000)) (7955065969 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((40989 / 512000) : ℝ) (4099 / 51200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1843501 / 500000) (1843567 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (40989 / 512000) (4099 / 51200) (234728763 / 200000000) (2934121 / 2500000) (1843501 / 500000) (1843567 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (40989 / 512000) (4099 / 51200) (1843501 / 500000) (1843567 / 500000) (32253 / 1000) (16129 / 500)
    (6053 / 125) (48499 / 1000) (-110297 / 200) (40489 / 100000) (1478583 / 500) (2011297 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1843501 / 500000) (7955065969 / 125000) (2011297 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843501 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843501 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell030 :
    ∀ t ∈ Set.Icc ((4099 / 51200) : ℝ) (40991 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173648399 / 1000000000) : ℝ) ≤ Real.exp (2 * (4099 / 51200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4099 / 51200)) (1173648399 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((40991 / 512000) : ℝ)) ≤ (234730597 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (40991 / 512000)) (234730597 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63643200709 / 1000000) : ℝ) ≤ Real.exp (3 * (460877 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (460877 / 125000)) (63643200709 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4099 / 51200) : ℝ) (40991 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (460877 / 125000) (3687149 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (4099 / 51200) (40991 / 512000) (1173648399 / 1000000000) (234730597 / 200000000) (460877 / 125000) (3687149 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (4099 / 51200) (40991 / 512000) (460877 / 125000) (3687149 / 1000000) (32253 / 1000) (32259 / 1000)
    (24213 / 500) (48501 / 1000) (-137871 / 250) (202439 / 500000) (1478607 / 500) (160897 / 40000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (460877 / 125000) (63643200709 / 1000000) (160897 / 40000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (460877 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (460877 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell031 :
    ∀ t ∈ Set.Icc ((40991 / 512000) : ℝ) (1281 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((146706623 / 125000000) : ℝ) ≤ Real.exp (2 * (40991 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (40991 / 512000)) (146706623 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1281 / 16000) : ℝ)) ≤ (117365757 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1281 / 16000)) (117365757 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63645873779 / 1000000) : ℝ) ≤ Real.exp (3 * (368703 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (368703 / 100000)) (63645873779 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((40991 / 512000) : ℝ) (1281 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (368703 / 100000) (3687163 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (40991 / 512000) (1281 / 16000) (146706623 / 125000000) (117365757 / 100000000) (368703 / 100000) (3687163 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (40991 / 512000) (1281 / 16000) (368703 / 100000) (3687163 / 1000000) (32253 / 1000) (32259 / 1000)
    (48427 / 1000) (48503 / 1000) (-275743 / 500) (202433 / 500000) (2957259 / 1000) (4022257 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (368703 / 100000) (63645873779 / 1000000) (4022257 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (368703 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (368703 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell032 :
    ∀ t ∈ Set.Icc ((1281 / 16000) : ℝ) (40993 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173657569 / 1000000000) : ℝ) ≤ Real.exp (2 * (1281 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1281 / 16000)) (1173657569 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((40993 / 512000) : ℝ)) ≤ (586831077 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (40993 / 512000)) (586831077 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31824368953 / 500000) : ℝ) ≤ Real.exp (3 * (737409 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (737409 / 200000)) (31824368953 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1281 / 16000) : ℝ) (40993 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (737409 / 200000) (1843589 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1281 / 16000) (40993 / 512000) (1173657569 / 1000000000) (586831077 / 500000000) (737409 / 200000) (1843589 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1281 / 16000) (40993 / 512000) (737409 / 200000) (1843589 / 500000) (16127 / 500) (32259 / 1000)
    (48429 / 1000) (9701 / 200) (-551489 / 1000) (404853 / 1000000) (2957307 / 1000) (1005519 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (737409 / 200000) (31824368953 / 500000) (1005519 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (737409 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (737409 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell033 :
    ∀ t ∈ Set.Icc ((40993 / 512000) : ℝ) (20497 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173662153 / 1000000000) : ℝ) ≤ Real.exp (2 * (40993 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (40993 / 512000)) (1173662153 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20497 / 256000) : ℝ)) ≤ (1173666739 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20497 / 256000)) (1173666739 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((7956426401 / 125000) : ℝ) ≤ Real.exp (3 * (3687059 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3687059 / 1000000)) (7956426401 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((40993 / 512000) : ℝ) (20497 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3687059 / 1000000) (460899 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (40993 / 512000) (20497 / 256000) (1173662153 / 1000000000) (1173666739 / 1000000000) (3687059 / 1000000) (460899 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (40993 / 512000) (20497 / 256000) (3687059 / 1000000) (460899 / 125000) (16127 / 500) (1613 / 50)
    (48431 / 1000) (48507 / 1000) (-551491 / 1000) (10121 / 25000) (369669 / 125) (4021907 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3687059 / 1000000) (7956426401 / 125000) (4021907 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687059 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687059 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell034 :
    ∀ t ∈ Set.Icc ((20497 / 256000) : ℝ) (8199 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((586833369 / 500000000) : ℝ) ≤ Real.exp (2 * (20497 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20497 / 256000)) (586833369 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8199 / 102400) : ℝ)) ≤ (1173671323 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8199 / 102400)) (1173671323 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((12730855117 / 200000) : ℝ) ≤ Real.exp (3 * (1843537 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1843537 / 500000)) (12730855117 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20497 / 256000) : ℝ) (8199 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1843537 / 500000) (1843603 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20497 / 256000) (8199 / 102400) (586833369 / 500000000) (1173671323 / 1000000000) (1843537 / 500000) (1843603 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20497 / 256000) (8199 / 102400) (1843537 / 500000) (1843603 / 500000) (16127 / 500) (1613 / 50)
    (48433 / 1000) (12127 / 250) (-275749 / 500) (202413 / 500000) (2957397 / 1000) (2010863 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1843537 / 500000) (12730855117 / 200000) (2010863 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843537 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843537 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell035 :
    ∀ t ∈ Set.Icc ((8199 / 102400) : ℝ) (10249 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((586835661 / 500000000) : ℝ) ≤ Real.exp (2 * (8199 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8199 / 102400)) (586835661 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((10249 / 128000) : ℝ)) ≤ (293418977 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (10249 / 128000)) (293418977 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((198927966 / 3125) : ℝ) ≤ Real.exp (3 * (230443 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (230443 / 62500)) (198927966 / 3125) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8199 / 102400) : ℝ) (10249 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (230443 / 62500) (3687221 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8199 / 102400) (10249 / 128000) (586835661 / 500000000) (293418977 / 250000000) (230443 / 62500) (3687221 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8199 / 102400) (10249 / 128000) (230443 / 62500) (3687221 / 1000000) (6451 / 200) (1613 / 50)
    (24217 / 500) (4851 / 100) (-551497 / 1000) (202407 / 500000) (591489 / 200) (4021557 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (230443 / 62500) (198927966 / 3125) (4021557 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (230443 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (230443 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell036 :
    ∀ t ∈ Set.Icc ((10249 / 128000) : ℝ) (40997 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173675907 / 1000000000) : ℝ) ≤ Real.exp (2 * (10249 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (10249 / 128000)) (1173675907 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((40997 / 512000) : ℝ)) ≤ (1173680493 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (40997 / 512000)) (1173680493 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31829811383 / 500000) : ℝ) ≤ Real.exp (3 * (1843551 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1843551 / 500000)) (31829811383 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((10249 / 128000) : ℝ) (40997 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1843551 / 500000) (737447 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (10249 / 128000) (40997 / 512000) (1173675907 / 1000000000) (1173680493 / 1000000000) (1843551 / 500000) (737447 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (10249 / 128000) (40997 / 512000) (1843551 / 500000) (737447 / 200000) (6451 / 200) (32261 / 1000)
    (12109 / 250) (6064 / 125) (-551499 / 1000) (202401 / 500000) (295749 / 100) (1005347 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1843551 / 500000) (31829811383 / 500000) (1005347 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843551 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843551 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell037 :
    ∀ t ∈ Set.Icc ((40997 / 512000) : ℝ) (20499 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293420123 / 250000000) : ℝ) ≤ Real.exp (2 * (40997 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (40997 / 512000)) (293420123 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20499 / 256000) : ℝ)) ≤ (1173685077 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20499 / 256000)) (1173685077 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63662487513 / 1000000) : ℝ) ≤ Real.exp (3 * (3687117 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3687117 / 1000000)) (63662487513 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((40997 / 512000) : ℝ) (20499 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3687117 / 1000000) (14749 / 4000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (40997 / 512000) (20499 / 256000) (293420123 / 250000000) (1173685077 / 1000000000) (3687117 / 1000000) (14749 / 4000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (40997 / 512000) (20499 / 256000) (3687117 / 1000000) (14749 / 4000) (6451 / 200) (32261 / 1000)
    (24219 / 500) (24257 / 500) (-275751 / 500) (404789 / 1000000) (1478769 / 500) (4021207 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3687117 / 1000000) (63662487513 / 1000000) (4021207 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687117 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687117 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell038 :
    ∀ t ∈ Set.Icc ((20499 / 256000) : ℝ) (40999 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293421269 / 250000000) : ℝ) ≤ Real.exp (2 * (20499 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20499 / 256000)) (293421269 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((40999 / 512000) : ℝ)) ≤ (586844831 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (40999 / 512000)) (586844831 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3979072587 / 62500) : ℝ) ≤ Real.exp (3 * (3687131 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3687131 / 1000000)) (3979072587 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20499 / 256000) : ℝ) (40999 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3687131 / 1000000) (115227 / 31250) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20499 / 256000) (40999 / 512000) (293421269 / 250000000) (586844831 / 500000000) (3687131 / 1000000) (115227 / 31250) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20499 / 256000) (40999 / 512000) (3687131 / 1000000) (115227 / 31250) (4032 / 125) (32261 / 1000)
    (48439 / 1000) (9703 / 200) (-68938 / 125) (50597 / 125000) (2957583 / 1000) (2010519 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3687131 / 1000000) (3979072587 / 62500) (2010519 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687131 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687131 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell039 :
    ∀ t ∈ Set.Icc ((40999 / 512000) : ℝ) (41 / 512), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173689661 / 1000000000) : ℝ) ≤ Real.exp (2 * (40999 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (40999 / 512000)) (1173689661 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41 / 512) : ℝ)) ≤ (1173694247 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41 / 512)) (1173694247 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15917006597 / 250000) : ℝ) ≤ Real.exp (3 * (1843573 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1843573 / 500000)) (15917006597 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((40999 / 512000) : ℝ) (41 / 512),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1843573 / 500000) (1843639 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (40999 / 512000) (41 / 512) (1173689661 / 1000000000) (1173694247 / 1000000000) (1843573 / 500000) (1843639 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (40999 / 512000) (41 / 512) (1843573 / 500000) (1843639 / 500000) (4032 / 125) (16131 / 500)
    (48441 / 1000) (48517 / 1000) (-551511 / 1000) (404763 / 1000000) (739407 / 250) (4020857 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1843573 / 500000) (15917006597 / 250000) (4020857 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843573 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843573 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch001 :
    ∀ t ∈ Set.Icc ((2049 / 25600) : ℝ) (41 / 512),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell020
      hpThetaDensityLowerExpCompact_cell021)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell022
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell023
      hpThetaDensityLowerExpCompact_cell024)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell025
      hpThetaDensityLowerExpCompact_cell026)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell027
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell028
      hpThetaDensityLowerExpCompact_cell029))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell030
      hpThetaDensityLowerExpCompact_cell031)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell032
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell033
      hpThetaDensityLowerExpCompact_cell034)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell035
      hpThetaDensityLowerExpCompact_cell036)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell037
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell038
      hpThetaDensityLowerExpCompact_cell039)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch001
end HodgeProofHP
