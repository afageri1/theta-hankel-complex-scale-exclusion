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
theorem hpThetaDensityLowerExpCompact_cell920 :
    ∀ t ∈ Set.Icc ((48147 / 512000) : ℝ) (48179 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((75432693 / 62500000) : ℝ) ≤ Real.exp (2 * (48147 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (48147 / 512000)) (75432693 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((48179 / 512000) : ℝ)) ≤ (301768491 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (48179 / 512000)) (301768491 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((43542659379 / 500000) : ℝ) ≤ Real.exp (3 * (947887 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (947887 / 250000)) (43542659379 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((48147 / 512000) : ℝ) (48179 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (947887 / 250000) (237009 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (48147 / 512000) (48179 / 512000) (75432693 / 62500000) (301768491 / 250000000) (947887 / 250000) (237009 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (48147 / 512000) (48179 / 512000) (947887 / 250000) (237009 / 62500) (139 / 4) (34773 / 1000)
    (12303 / 200) (61867 / 1000) (-565457 / 1000) (64379 / 200000) (661743 / 200) (1469823 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (947887 / 250000) (43542659379 / 500000) (1469823 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (947887 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (947887 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell921 :
    ∀ t ∈ Set.Icc ((48179 / 512000) : ℝ) (48211 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1207073963 / 1000000000) : ℝ) ≤ Real.exp (2 * (48179 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (48179 / 512000)) (1207073963 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((48211 / 512000) : ℝ)) ≤ (1207224857 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (48211 / 512000)) (1207224857 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((21802310519 / 250000) : ℝ) ≤ Real.exp (3 * (1896011 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1896011 / 500000)) (21802310519 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((48179 / 512000) : ℝ) (48211 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1896011 / 500000) (1896309 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (48179 / 512000) (48211 / 512000) (1207073963 / 1000000000) (1207224857 / 1000000000) (1896011 / 500000) (1896309 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (48179 / 512000) (48211 / 512000) (1896011 / 500000) (1896309 / 500000) (17381 / 500) (4348 / 125)
    (30789 / 500) (6193 / 100) (-565517 / 1000) (160779 / 500000) (3310369 / 1000) (2935469 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1896011 / 500000) (21802310519 / 250000) (2935469 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1896011 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1896011 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell922 :
    ∀ t ∈ Set.Icc ((48211 / 512000) : ℝ) (48243 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((150903107 / 125000000) : ℝ) ≤ Real.exp (2 * (48211 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (48211 / 512000)) (150903107 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((48243 / 512000) : ℝ)) ≤ (120737577 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (48243 / 512000)) (120737577 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((43666670869 / 500000) : ℝ) ≤ Real.exp (3 * (237031 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (237031 / 62500)) (43666670869 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((48211 / 512000) : ℝ) (48243 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (237031 / 62500) (948273 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (48211 / 512000) (48243 / 512000) (150903107 / 125000000) (120737577 / 100000000) (237031 / 62500) (948273 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (48211 / 512000) (48243 / 512000) (237031 / 62500) (948273 / 250000) (34773 / 1000) (8699 / 250)
    (61641 / 1000) (7749 / 125) (-70697 / 125) (321221 / 1000000) (132481 / 40) (1465649 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (237031 / 62500) (43666670869 / 500000) (1465649 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (237031 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (237031 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell923 :
    ∀ t ∈ Set.Icc ((48243 / 512000) : ℝ) (1931 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1207375769 / 1000000000) : ℝ) ≤ Real.exp (2 * (48243 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (48243 / 512000)) (1207375769 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1931 / 20480) : ℝ)) ≤ (1207526701 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1931 / 20480)) (1207526701 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((43728808997 / 500000) : ℝ) ≤ Real.exp (3 * (379297 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (379297 / 100000)) (43728808997 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((48243 / 512000) : ℝ) (1931 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (379297 / 100000) (1896783 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (48243 / 512000) (1931 / 20480) (1207375769 / 1000000000) (1207526701 / 1000000000) (379297 / 100000) (1896783 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (48243 / 512000) (1931 / 20480) (379297 / 100000) (1896783 / 500000) (6957 / 200) (34807 / 1000)
    (7713 / 125) (12411 / 200) (-141409 / 250) (64177 / 200000) (82842 / 25) (2927133 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (379297 / 100000) (43728808997 / 500000) (2927133 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (379297 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (379297 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell924 :
    ∀ t ∈ Set.Icc ((1931 / 20480) : ℝ) (48307 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((12075267 / 10000000) : ℝ) ≤ Real.exp (2 * (1931 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1931 / 20480)) (12075267 / 10000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((48307 / 512000) : ℝ)) ≤ (301919413 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (48307 / 512000)) (301919413 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((21895583461 / 250000) : ℝ) ≤ Real.exp (3 * (758689 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (758689 / 200000)) (21895583461 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1931 / 20480) : ℝ) (48307 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (758689 / 200000) (3794041 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1931 / 20480) (48307 / 512000) (12075267 / 10000000) (301919413 / 250000000) (758689 / 200000) (3794041 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1931 / 20480) (48307 / 512000) (758689 / 200000) (3794041 / 1000000) (8699 / 250) (34819 / 1000)
    (61767 / 1000) (31059 / 500) (-70712 / 125) (320549 / 1000000) (165767 / 50) (730741 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (758689 / 200000) (21895583461 / 250000) (730741 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (758689 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (758689 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell925 :
    ∀ t ∈ Set.Icc ((48307 / 512000) : ℝ) (48339 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1207677651 / 1000000000) : ℝ) ≤ Real.exp (2 * (48307 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (48307 / 512000)) (1207677651 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((48339 / 512000) : ℝ)) ≤ (1207828621 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (48339 / 512000)) (1207828621 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((43853482209 / 500000) : ℝ) ≤ Real.exp (3 * (3793919 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3793919 / 1000000)) (43853482209 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((48307 / 512000) : ℝ) (48339 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3793919 / 1000000) (758903 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (48307 / 512000) (48339 / 512000) (1207677651 / 1000000000) (1207828621 / 1000000000) (3793919 / 1000000) (758903 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (48307 / 512000) (48339 / 512000) (3793919 / 1000000) (758903 / 200000) (4351 / 125) (3483 / 100)
    (6183 / 100) (62181 / 1000) (-113151 / 200) (320213 / 1000000) (3316997 / 1000) (2918811 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3793919 / 1000000) (43853482209 / 500000) (2918811 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3793919 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3793919 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell926 :
    ∀ t ∈ Set.Icc ((48339 / 512000) : ℝ) (48371 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((60391431 / 50000000) : ℝ) ≤ Real.exp (2 * (48339 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (48339 / 512000)) (60391431 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((48371 / 512000) : ℝ)) ≤ (1207979609 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (48371 / 512000)) (1207979609 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((87831772343 / 1000000) : ℝ) ≤ Real.exp (3 * (3794393 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3794393 / 1000000)) (87831772343 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((48339 / 512000) : ℝ) (48371 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3794393 / 1000000) (3794989 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (48339 / 512000) (48371 / 512000) (60391431 / 50000000) (1207979609 / 1000000000) (3794393 / 1000000) (3794989 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (48339 / 512000) (48371 / 512000) (3794393 / 1000000) (3794989 / 1000000) (34819 / 1000) (17421 / 500)
    (61893 / 1000) (15561 / 250) (-282907 / 500) (159939 / 500000) (663731 / 200) (2914663 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3794393 / 1000000) (87831772343 / 1000000) (2914663 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3794393 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3794393 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell927 :
    ∀ t ∈ Set.Icc ((48371 / 512000) : ℝ) (48403 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((150997451 / 125000000) : ℝ) ≤ Real.exp (2 * (48371 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (48371 / 512000)) (150997451 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((48403 / 512000) : ℝ)) ≤ (151016327 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (48403 / 512000)) (151016327 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((87956757871 / 1000000) : ℝ) ≤ Real.exp (3 * (3794867 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3794867 / 1000000)) (87956757871 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((48371 / 512000) : ℝ) (48403 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3794867 / 1000000) (474433 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (48371 / 512000) (48403 / 512000) (150997451 / 125000000) (151016327 / 125000000) (3794867 / 1000000) (474433 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (48371 / 512000) (48403 / 512000) (3794867 / 1000000) (474433 / 125000) (34831 / 1000) (34853 / 1000)
    (15489 / 250) (15577 / 250) (-141467 / 250) (319543 / 1000000) (3320317 / 1000) (1455261 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3794867 / 1000000) (87956757871 / 1000000) (1455261 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3794867 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3794867 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell928 :
    ∀ t ∈ Set.Icc ((48403 / 512000) : ℝ) (9687 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((241626123 / 200000000) : ℝ) ≤ Real.exp (2 * (48403 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (48403 / 512000)) (241626123 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9687 / 102400) : ℝ)) ≤ (1208281641 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9687 / 102400)) (1208281641 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((176164371 / 2000) : ℝ) ≤ Real.exp (3 * (1897671 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1897671 / 500000)) (176164371 / 2000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((48403 / 512000) : ℝ) (9687 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1897671 / 500000) (1897969 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (48403 / 512000) (9687 / 102400) (241626123 / 200000000) (1208281641 / 1000000000) (1897671 / 500000) (1897969 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (48403 / 512000) (9687 / 102400) (1897671 / 500000) (1897969 / 500000) (17421 / 500) (6973 / 200)
    (62019 / 1000) (62371 / 1000) (-141483 / 250) (39901 / 125000) (415247 / 125) (2906377 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1897671 / 500000) (176164371 / 2000) (2906377 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1897671 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1897671 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell929 :
    ∀ t ∈ Set.Icc ((9687 / 102400) : ℝ) (48467 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((30207041 / 25000000) : ℝ) ≤ Real.exp (2 * (9687 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9687 / 102400)) (30207041 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((48467 / 512000) : ℝ)) ≤ (604216343 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (48467 / 512000)) (604216343 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((11025940921 / 125000) : ℝ) ≤ Real.exp (3 * (474477 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (474477 / 125000)) (11025940921 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9687 / 102400) : ℝ) (48467 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (474477 / 125000) (3796413 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9687 / 102400) (48467 / 512000) (30207041 / 25000000) (604216343 / 500000000) (474477 / 125000) (3796413 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9687 / 102400) (48467 / 512000) (474477 / 125000) (3796413 / 1000000) (17427 / 500) (34877 / 1000)
    (31041 / 500) (31217 / 500) (-282993 / 500) (159437 / 500000) (3323639 / 1000) (2902247 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (474477 / 125000) (11025940921 / 125000) (2902247 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (474477 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (474477 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell930 :
    ∀ t ∈ Set.Icc ((48467 / 512000) : ℝ) (48499 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((241686537 / 200000000) : ℝ) ≤ Real.exp (2 * (48467 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (48467 / 512000)) (241686537 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((48499 / 512000) : ℝ)) ≤ (966867 / 800000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (48499 / 512000)) (966867 / 800000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((44166656299 / 500000) : ℝ) ≤ Real.exp (3 * (3796291 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3796291 / 1000000)) (44166656299 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((48467 / 512000) : ℝ) (48499 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3796291 / 1000000) (3796887 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (48467 / 512000) (48499 / 512000) (241686537 / 200000000) (966867 / 800000) (3796291 / 1000000) (3796887 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (48467 / 512000) (48499 / 512000) (3796291 / 1000000) (3796887 / 1000000) (6973 / 200) (4361 / 125)
    (12429 / 200) (62497 / 1000) (-11321 / 20) (318539 / 1000000) (3325299 / 1000) (1449057 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3796291 / 1000000) (44166656299 / 500000) (1449057 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3796291 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3796291 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell931 :
    ∀ t ∈ Set.Icc ((48499 / 512000) : ℝ) (48531 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1208583749 / 1000000000) : ℝ) ≤ Real.exp (2 * (48499 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (48499 / 512000)) (1208583749 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((48531 / 512000) : ℝ)) ≤ (75545927 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (48531 / 512000)) (75545927 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((44229505911 / 500000) : ℝ) ≤ Real.exp (3 * (759353 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (759353 / 200000)) (44229505911 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((48499 / 512000) : ℝ) (48531 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (759353 / 200000) (1898681 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (48499 / 512000) (48531 / 512000) (1208583749 / 1000000000) (75545927 / 62500000) (759353 / 200000) (1898681 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (48499 / 512000) (48531 / 512000) (759353 / 200000) (1898681 / 500000) (34877 / 1000) (349 / 10)
    (7776 / 125) (62561 / 1000) (-70763 / 125) (159103 / 500000) (831741 / 250) (723499 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (759353 / 200000) (44229505911 / 500000) (723499 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (759353 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (759353 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell932 :
    ∀ t ∈ Set.Icc ((48531 / 512000) : ℝ) (48563 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1208734831 / 1000000000) : ℝ) ≤ Real.exp (2 * (48531 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (48531 / 512000)) (1208734831 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((48563 / 512000) : ℝ)) ≤ (1208885933 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (48563 / 512000)) (1208885933 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((11073144459 / 125000) : ℝ) ≤ Real.exp (3 * (94931 / 25000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (94931 / 25000)) (11073144459 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((48531 / 512000) : ℝ) (48563 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (94931 / 25000) (3797837 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (48531 / 512000) (48563 / 512000) (1208734831 / 1000000000) (1208885933 / 1000000000) (94931 / 25000) (3797837 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (48531 / 512000) (48563 / 512000) (94931 / 25000) (3797837 / 1000000) (34889 / 1000) (34911 / 1000)
    (62271 / 1000) (7828 / 125) (-283081 / 500) (19867 / 62500) (3328629 / 1000) (23119 / 8000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (94931 / 25000) (11073144459 / 125000) (23119 / 8000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (94931 / 25000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (94931 / 25000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell933 :
    ∀ t ∈ Set.Icc ((48563 / 512000) : ℝ) (9719 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((302221483 / 250000000) : ℝ) ≤ Real.exp (2 * (48563 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (48563 / 512000)) (302221483 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9719 / 102400) : ℝ)) ≤ (1209037053 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9719 / 102400)) (1209037053 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((22177869851 / 250000) : ℝ) ≤ Real.exp (3 * (759543 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (759543 / 200000)) (22177869851 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((48563 / 512000) : ℝ) (9719 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (759543 / 200000) (3798311 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (48563 / 512000) (9719 / 102400) (302221483 / 250000000) (1209037053 / 1000000000) (759543 / 200000) (3798311 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (48563 / 512000) (9719 / 102400) (759543 / 200000) (3798311 / 1000000) (349 / 10) (34923 / 1000)
    (12467 / 200) (62687 / 1000) (-22649 / 40) (158769 / 500000) (3330291 / 1000) (4509 / 1562500)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (759543 / 200000) (22177869851 / 250000) (4509 / 1562500)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (759543 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (759543 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell934 :
    ∀ t ∈ Set.Icc ((9719 / 102400) : ℝ) (48627 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((302259263 / 250000000) : ℝ) ≤ Real.exp (2 * (9719 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9719 / 102400)) (302259263 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((48627 / 512000) : ℝ)) ≤ (1209188193 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (48627 / 512000)) (1209188193 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((44418858381 / 500000) : ℝ) ≤ Real.exp (3 * (3798189 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3798189 / 1000000)) (44418858381 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9719 / 102400) : ℝ) (48627 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3798189 / 1000000) (1899393 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9719 / 102400) (48627 / 512000) (302259263 / 250000000) (1209188193 / 1000000000) (3798189 / 1000000) (1899393 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9719 / 102400) (48627 / 512000) (3798189 / 1000000) (1899393 / 500000) (4364 / 125) (17467 / 500)
    (31199 / 500) (62751 / 1000) (-566279 / 1000) (158603 / 500000) (3331957 / 1000) (2881659 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3798189 / 1000000) (44418858381 / 500000) (2881659 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3798189 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3798189 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell935 :
    ∀ t ∈ Set.Icc ((48627 / 512000) : ℝ) (48659 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((37787131 / 31250000) : ℝ) ≤ Real.exp (2 * (48627 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (48627 / 512000)) (37787131 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((48659 / 512000) : ℝ)) ≤ (24186787 / 20000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (48659 / 512000)) (24186787 / 20000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1779288013 / 20000) : ℝ) ≤ Real.exp (3 * (474833 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (474833 / 125000)) (1779288013 / 20000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((48627 / 512000) : ℝ) (48659 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (474833 / 125000) (3799261 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (48627 / 512000) (48659 / 512000) (37787131 / 31250000) (24186787 / 20000000) (474833 / 125000) (3799261 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (48627 / 512000) (48659 / 512000) (474833 / 125000) (3799261 / 1000000) (34923 / 1000) (17473 / 500)
    (62461 / 1000) (31407 / 500) (-566337 / 1000) (316873 / 1000000) (416703 / 125) (719389 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (474833 / 125000) (1779288013 / 20000) (719389 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (474833 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (474833 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell936 :
    ∀ t ∈ Set.Icc ((48659 / 512000) : ℝ) (48691 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1209339349 / 1000000000) : ℝ) ≤ Real.exp (2 * (48659 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (48659 / 512000)) (1209339349 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((48691 / 512000) : ℝ)) ≤ (1209490527 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (48691 / 512000)) (1209490527 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((89091265191 / 1000000) : ℝ) ≤ Real.exp (3 * (3799139 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3799139 / 1000000)) (89091265191 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((48659 / 512000) : ℝ) (48691 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3799139 / 1000000) (474967 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (48659 / 512000) (48691 / 512000) (1209339349 / 1000000000) (1209490527 / 1000000000) (3799139 / 1000000) (474967 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (48659 / 512000) (48691 / 512000) (3799139 / 1000000) (474967 / 125000) (6987 / 200) (17479 / 500)
    (15631 / 250) (62877 / 1000) (-113279 / 200) (316541 / 1000000) (3335291 / 1000) (1436729 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3799139 / 1000000) (89091265191 / 1000000) (1436729 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3799139 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3799139 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell937 :
    ∀ t ∈ Set.Icc ((48691 / 512000) : ℝ) (48723 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((604745263 / 500000000) : ℝ) ≤ Real.exp (2 * (48691 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (48691 / 512000)) (604745263 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((48723 / 512000) : ℝ)) ≤ (1209641723 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (48723 / 512000)) (1209641723 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((44609155321 / 500000) : ℝ) ≤ Real.exp (3 * (1899807 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1899807 / 500000)) (44609155321 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((48691 / 512000) : ℝ) (48723 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1899807 / 500000) (3800211 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (48691 / 512000) (48723 / 512000) (604745263 / 500000000) (1209641723 / 1000000000) (1899807 / 500000) (3800211 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (48691 / 512000) (48723 / 512000) (1899807 / 500000) (3800211 / 1000000) (34947 / 1000) (34969 / 1000)
    (15647 / 250) (62941 / 1000) (-566453 / 1000) (316209 / 1000000) (3336959 / 1000) (2869367 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1899807 / 500000) (44609155321 / 500000) (2869367 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1899807 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1899807 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell938 :
    ∀ t ∈ Set.Icc ((48723 / 512000) : ℝ) (9751 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((604820861 / 500000000) : ℝ) ≤ Real.exp (2 * (48723 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (48723 / 512000)) (604820861 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9751 / 102400) : ℝ)) ≤ (604896469 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9751 / 102400)) (604896469 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((44672768631 / 500000) : ℝ) ≤ Real.exp (3 * (3800089 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3800089 / 1000000)) (44672768631 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((48723 / 512000) : ℝ) (9751 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3800089 / 1000000) (1900343 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (48723 / 512000) (9751 / 102400) (604820861 / 500000000) (604896469 / 500000000) (3800089 / 1000000) (1900343 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (48723 / 512000) (9751 / 102400) (3800089 / 1000000) (1900343 / 500000) (17479 / 500) (34981 / 1000)
    (62651 / 1000) (15751 / 250) (-566511 / 1000) (315877 / 1000000) (834657 / 250) (2865281 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3800089 / 1000000) (44672768631 / 500000) (2865281 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3800089 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3800089 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell939 :
    ∀ t ∈ Set.Icc ((9751 / 102400) : ℝ) (48787 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1209792937 / 1000000000) : ℝ) ≤ Real.exp (2 * (9751 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9751 / 102400)) (1209792937 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((48787 / 512000) : ℝ)) ≤ (1209944171 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (48787 / 512000)) (1209944171 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((22368236327 / 250000) : ℝ) ≤ Real.exp (3 * (950141 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (950141 / 250000)) (22368236327 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9751 / 102400) : ℝ) (48787 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (950141 / 250000) (3801161 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9751 / 102400) (48787 / 512000) (1209792937 / 1000000000) (1209944171 / 1000000000) (950141 / 250000) (3801161 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9751 / 102400) (48787 / 512000) (950141 / 250000) (3801161 / 1000000) (3497 / 100) (4374 / 125)
    (12543 / 200) (15767 / 250) (-566569 / 1000) (63109 / 200000) (3340297 / 1000) (2861201 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (950141 / 250000) (22368236327 / 250000) (2861201 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (950141 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (950141 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch046 :
    ∀ t ∈ Set.Icc ((48147 / 512000) : ℝ) (48787 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell920
      hpThetaDensityLowerExpCompact_cell921)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell922
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell923
      hpThetaDensityLowerExpCompact_cell924)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell925
      hpThetaDensityLowerExpCompact_cell926)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell927
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell928
      hpThetaDensityLowerExpCompact_cell929))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell930
      hpThetaDensityLowerExpCompact_cell931)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell932
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell933
      hpThetaDensityLowerExpCompact_cell934)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell935
      hpThetaDensityLowerExpCompact_cell936)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell937
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell938
      hpThetaDensityLowerExpCompact_cell939)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch046
end HodgeProofHP
