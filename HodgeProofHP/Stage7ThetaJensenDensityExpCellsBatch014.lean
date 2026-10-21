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
theorem hpThetaDensityExpCompact_cell280 :
    ∀ t ∈ Set.Icc ((469 / 3200) : ℝ) (2349 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((335152589 / 250000000) : ℝ) ≤ Real.exp (2 * (469 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (469 / 3200)) (335152589 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2349 / 16000) : ℝ)) ≤ (134128083 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2349 / 16000)) (134128083 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((306992154249 / 1000000) : ℝ) ≤ Real.exp (3 * (4211527 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4211527 / 1000000)) (306992154249 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((469 / 3200) : ℝ) (2349 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4211527 / 1000000) (526721 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (469 / 3200) (2349 / 16000) (335152589 / 250000000) (134128083 / 100000000) (4211527 / 1000000) (526721 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (469 / 3200) (2349 / 16000) (4211527 / 1000000) (526721 / 125000) (9133 / 200) (9151 / 200)
    (25619 / 200) (2593 / 20) (-110053 / 200) (62641 / 500000) (5044319 / 1000) (416949 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4211527 / 1000000) (306992154249 / 1000000) (416949 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4211527 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4211527 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell281 :
    ∀ t ∈ Set.Icc ((2349 / 16000) : ℝ) (2353 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1341280829 / 1000000000) : ℝ) ≤ Real.exp (2 * (2349 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2349 / 16000)) (1341280829 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2353 / 16000) : ℝ)) ≤ (670975819 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2353 / 16000)) (670975819 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((154468929897 / 500000) : ℝ) ≤ Real.exp (3 * (4213633 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4213633 / 1000000)) (154468929897 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2349 / 16000) : ℝ) (2353 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4213633 / 1000000) (1053969 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2349 / 16000) (2353 / 16000) (1341280829 / 1000000000) (670975819 / 500000000) (4213633 / 1000000) (1053969 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2349 / 16000) (2353 / 16000) (4213633 / 1000000) (1053969 / 250000) (45723 / 1000) (45813 / 1000)
    (12849 / 100) (16256 / 125) (-549867 / 1000) (3117 / 25000) (252721 / 50) (414323 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4213633 / 1000000) (154468929897 / 500000) (414323 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4213633 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4213633 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell282 :
    ∀ t ∈ Set.Icc ((2353 / 16000) : ℝ) (2357 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1341951637 / 1000000000) : ℝ) ≤ Real.exp (2 * (2353 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2353 / 16000)) (1341951637 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2357 / 16000) : ℝ)) ≤ (1342622781 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2357 / 16000)) (1342622781 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((155448881211 / 500000) : ℝ) ≤ Real.exp (3 * (4215741 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4215741 / 1000000)) (155448881211 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2353 / 16000) : ℝ) (2357 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4215741 / 1000000) (65906 / 15625) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2353 / 16000) (2357 / 16000) (1341951637 / 1000000000) (1342622781 / 1000000000) (4215741 / 1000000) (65906 / 15625) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2353 / 16000) (2357 / 16000) (4215741 / 1000000) (65906 / 15625) (45781 / 1000) (5734 / 125)
    (128887 / 1000) (65223 / 500) (-274739 / 500) (1551 / 12500) (5064537 / 1000) (411711 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4215741 / 1000000) (155448881211 / 500000) (411711 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4215741 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4215741 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell283 :
    ∀ t ∈ Set.Icc ((2357 / 16000) : ℝ) (2361 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((67131139 / 50000000) : ℝ) ≤ Real.exp (2 * (2357 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2357 / 16000)) (67131139 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2361 / 16000) : ℝ)) ≤ (67164713 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2361 / 16000)) (67164713 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((156435049287 / 500000) : ℝ) ≤ Real.exp (3 * (4217849 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4217849 / 1000000)) (156435049287 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2357 / 16000) : ℝ) (2361 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4217849 / 1000000) (2110047 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2357 / 16000) (2361 / 16000) (67131139 / 50000000) (67164713 / 50000000) (4217849 / 1000000) (2110047 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2357 / 16000) (2361 / 16000) (4217849 / 1000000) (2110047 / 500000) (1146 / 25) (4593 / 100)
    (32321 / 250) (65423 / 500) (-68634 / 125) (123483 / 1000000) (2537339 / 500) (818231 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4217849 / 1000000) (156435049287 / 500000) (818231 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4217849 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4217849 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell284 :
    ∀ t ∈ Set.Icc ((2361 / 16000) : ℝ) (473 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1343294259 / 1000000000) : ℝ) ≤ Real.exp (2 * (2361 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2361 / 16000)) (1343294259 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((473 / 3200) : ℝ)) ≤ (335991519 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (473 / 3200)) (335991519 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((39356986461 / 125000) : ℝ) ≤ Real.exp (3 * (2109979 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2109979 / 500000)) (39356986461 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2361 / 16000) : ℝ) (473 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2109979 / 500000) (1055551 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2361 / 16000) (473 / 3200) (1343294259 / 1000000000) (335991519 / 250000000) (2109979 / 500000) (1055551 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2361 / 16000) (473 / 3200) (2109979 / 500000) (1055551 / 250000) (22949 / 500) (45989 / 1000)
    (64841 / 500) (65623 / 500) (-137167 / 250) (122889 / 1000000) (1016967 / 200) (813071 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2109979 / 500000) (39356986461 / 125000) (813071 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2109979 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2109979 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell285 :
    ∀ t ∈ Set.Icc ((473 / 3200) : ℝ) (2369 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((53758643 / 40000000) : ℝ) ≤ Real.exp (2 * (473 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (473 / 3200)) (53758643 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2369 / 16000) : ℝ)) ≤ (1344638227 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2369 / 16000)) (1344638227 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((316856189687 / 1000000) : ℝ) ≤ Real.exp (3 * (4222069 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4222069 / 1000000)) (316856189687 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((473 / 3200) : ℝ) (2369 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4222069 / 1000000) (1056079 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (473 / 3200) (2369 / 16000) (53758643 / 40000000) (1344638227 / 1000000000) (4222069 / 1000000) (1056079 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (473 / 3200) (2369 / 16000) (4222069 / 1000000) (1056079 / 250000) (45957 / 1000) (46047 / 1000)
    (130081 / 1000) (131647 / 1000) (-27413 / 50) (15287 / 125000) (5095017 / 1000) (403969 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4222069 / 1000000) (316856189687 / 1000000) (403969 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4222069 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4222069 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell286 :
    ∀ t ∈ Set.Icc ((2369 / 16000) : ℝ) (2373 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((672319113 / 500000000) : ℝ) ≤ Real.exp (2 * (2369 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2369 / 16000)) (672319113 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2373 / 16000) : ℝ)) ≤ (672655357 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2373 / 16000)) (672655357 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((79717298897 / 250000) : ℝ) ≤ Real.exp (3 * (211209 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (211209 / 50000)) (79717298897 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2369 / 16000) : ℝ) (2373 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (211209 / 50000) (4226429 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2369 / 16000) (2373 / 16000) (672319113 / 500000000) (672655357 / 500000000) (211209 / 50000) (4226429 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2369 / 16000) (2373 / 16000) (211209 / 50000) (4226429 / 1000000) (5752 / 125) (23053 / 500)
    (130481 / 1000) (2641 / 20) (-547841 / 1000) (121707 / 1000000) (5105219 / 1000) (401419 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (211209 / 50000) (79717298897 / 250000) (401419 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (211209 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (211209 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell287 :
    ∀ t ∈ Set.Icc ((2373 / 16000) : ℝ) (2377 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1345310713 / 1000000000) : ℝ) ≤ Real.exp (2 * (2373 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2373 / 16000)) (1345310713 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2377 / 16000) : ℝ)) ≤ (1345983537 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2377 / 16000)) (1345983537 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((10028028609 / 31250) : ℝ) ≤ Real.exp (3 * (4226293 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4226293 / 1000000)) (10028028609 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2373 / 16000) : ℝ) (2377 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4226293 / 1000000) (2114271 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2373 / 16000) (2377 / 16000) (1345310713 / 1000000000) (1345983537 / 1000000000) (4226293 / 1000000) (2114271 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2373 / 16000) (2377 / 16000) (4226293 / 1000000) (2114271 / 500000) (23037 / 500) (9233 / 200)
    (65441 / 500) (33113 / 250) (-54743 / 100) (121119 / 1000000) (1278859 / 250) (199441 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4226293 / 1000000) (10028028609 / 31250) (199441 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4226293 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4226293 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell288 :
    ∀ t ∈ Set.Icc ((2377 / 16000) : ℝ) (2381 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((84123971 / 62500000) : ℝ) ≤ Real.exp (2 * (2377 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2377 / 16000)) (84123971 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2381 / 16000) : ℝ)) ≤ (1346656697 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2381 / 16000)) (1346656697 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((322938498551 / 1000000) : ℝ) ≤ Real.exp (3 * (4228407 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4228407 / 1000000)) (322938498551 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2377 / 16000) : ℝ) (2381 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4228407 / 1000000) (4230657 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2377 / 16000) (2381 / 16000) (84123971 / 62500000) (1346656697 / 1000000000) (4228407 / 1000000) (4230657 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2377 / 16000) (2381 / 16000) (4228407 / 1000000) (4230657 / 1000000) (46133 / 1000) (5778 / 125)
    (32821 / 250) (26571 / 200) (-547009 / 1000) (60267 / 500000) (2562839 / 500) (792721 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4228407 / 1000000) (322938498551 / 1000000) (792721 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4228407 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4228407 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell289 :
    ∀ t ∈ Set.Icc ((2381 / 16000) : ℝ) (477 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((168332087 / 125000000) : ℝ) ≤ Real.exp (2 * (2381 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2381 / 16000)) (168332087 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((477 / 3200) : ℝ)) ≤ (673665097 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (477 / 3200)) (673665097 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((162497022631 / 500000) : ℝ) ≤ Real.exp (3 * (2115261 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2115261 / 500000)) (162497022631 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2381 / 16000) : ℝ) (477 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2115261 / 500000) (4232773 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2381 / 16000) (477 / 3200) (168332087 / 125000000) (673665097 / 500000000) (2115261 / 500000) (4232773 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2381 / 16000) (477 / 3200) (2115261 / 500000) (4232773 / 1000000) (5774 / 125) (46283 / 1000)
    (65843 / 500) (6663 / 50) (-546583 / 1000) (119951 / 1000000) (256797 / 50) (787707 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2115261 / 500000) (162497022631 / 500000) (787707 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2115261 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2115261 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell290 :
    ∀ t ∈ Set.Icc ((477 / 3200) : ℝ) (1911 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1347330193 / 1000000000) : ℝ) ≤ Real.exp (2 * (477 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (477 / 3200)) (1347330193 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1911 / 12800) : ℝ)) ≤ (1347961903 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1911 / 12800)) (1347961903 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((327062675687 / 1000000) : ℝ) ≤ Real.exp (3 * (4232637 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4232637 / 1000000)) (327062675687 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((477 / 3200) : ℝ) (1911 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4232637 / 1000000) (2117379 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (477 / 3200) (1911 / 12800) (1347330193 / 1000000000) (1347961903 / 1000000000) (4232637 / 1000000) (2117379 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (477 / 3200) (1911 / 12800) (4232637 / 1000000) (2117379 / 500000) (11563 / 250) (46337 / 1000)
    (132123 / 1000) (133607 / 1000) (-546973 / 1000) (373 / 3125) (5145581 / 1000) (31309 / 40000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4232637 / 1000000) (327062675687 / 1000000) (31309 / 40000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4232637 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4232637 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell291 :
    ∀ t ∈ Set.Icc ((1911 / 12800) : ℝ) (3831 / 25600), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((673980951 / 500000000) : ℝ) ≤ Real.exp (2 * (1911 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1911 / 12800)) (673980951 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3831 / 25600) : ℝ)) ≤ (674455011 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3831 / 25600)) (674455011 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((329016132579 / 1000000) : ℝ) ≤ Real.exp (3 * (2117311 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2117311 / 500000)) (329016132579 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1911 / 12800) : ℝ) (3831 / 25600),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2117311 / 500000) (529717 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1911 / 12800) (3831 / 25600) (673980951 / 500000000) (674455011 / 500000000) (2117311 / 500000) (529717 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1911 / 12800) (3831 / 25600) (2117311 / 500000) (529717 / 125000) (46301 / 1000) (23213 / 500)
    (132249 / 1000) (13443 / 100) (-540349 / 1000) (59451 / 500000) (516007 / 100) (389039 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2117311 / 500000) (329016132579 / 1000000) (389039 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2117311 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2117311 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell292 :
    ∀ t ∈ Set.Icc ((3831 / 25600) : ℝ) (3 / 20), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1348910021 / 1000000000) : ℝ) ≤ Real.exp (2 * (3831 / 25600)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3831 / 25600)) (1348910021 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3 / 20) : ℝ)) ≤ (168732351 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3 / 20)) (168732351 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((20748044621 / 62500) : ℝ) ≤ Real.exp (3 * (5297 / 1250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5297 / 1250)) (20748044621 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3831 / 25600) : ℝ) (3 / 20),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5297 / 1250) (4240717 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (3831 / 25600) (3 / 20) (1348910021 / 1000000000) (168732351 / 125000000) (5297 / 1250) (4240717 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (3831 / 25600) (3 / 20) (5297 / 1250) (4240717 / 1000000) (5798 / 125) (4651 / 100)
    (66409 / 500) (135003 / 1000) (-67464 / 125) (59047 / 500000) (1034921 / 200) (385579 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5297 / 1250) (20748044621 / 62500) (385579 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5297 / 1250)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5297 / 1250)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityExpCompact_cellsBatch014 :
    ∀ t ∈ Set.Icc ((469 / 3200) : ℝ) (3 / 20),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell280
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell281
      hpThetaDensityExpCompact_cell282))
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell283
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell284
      hpThetaDensityExpCompact_cell285)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell286
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell287
      hpThetaDensityExpCompact_cell288))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell289
      hpThetaDensityExpCompact_cell290)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell291
      hpThetaDensityExpCompact_cell292))))

#print axioms hpThetaDensityExpCompact_cellsBatch014
end HodgeProofHP
