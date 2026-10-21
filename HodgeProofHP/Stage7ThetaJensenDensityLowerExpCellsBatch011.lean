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
theorem hpThetaDensityLowerExpCompact_cell220 :
    ∀ t ∈ Set.Icc ((41247 / 512000) : ℝ) (41249 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((146853403 / 125000000) : ℝ) ≤ Real.exp (2 * (41247 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41247 / 512000)) (146853403 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41249 / 512000) : ℝ)) ≤ (1174836403 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41249 / 512000)) (1174836403 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32177077197 / 500000) : ℝ) ≤ Real.exp (3 * (3690719 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3690719 / 1000000)) (32177077197 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41247 / 512000) : ℝ) (41249 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3690719 / 1000000) (3690867 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41247 / 512000) (41249 / 512000) (146853403 / 125000000) (1174836403 / 1000000000) (3690719 / 1000000) (3690867 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41247 / 512000) (41249 / 512000) (3690719 / 1000000) (3690867 / 1000000) (1617 / 50) (16173 / 500)
    (12217 / 250) (6119 / 125) (-552081 / 1000) (200809 / 500000) (74229 / 25) (994497 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3690719 / 1000000) (32177077197 / 500000) (994497 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690719 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690719 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell221 :
    ∀ t ∈ Set.Icc ((41249 / 512000) : ℝ) (41251 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587418201 / 500000000) : ℝ) ≤ Real.exp (2 * (41249 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41249 / 512000)) (587418201 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41251 / 512000) : ℝ)) ≤ (587422791 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41251 / 512000)) (587422791 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64359753447 / 1000000) : ℝ) ≤ Real.exp (3 * (922687 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (922687 / 250000)) (64359753447 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41249 / 512000) : ℝ) (41251 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (922687 / 250000) (738179 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41249 / 512000) (41251 / 512000) (587418201 / 500000000) (587422791 / 500000000) (922687 / 250000) (738179 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41249 / 512000) (41251 / 512000) (922687 / 250000) (738179 / 200000) (32341 / 1000) (32347 / 1000)
    (48871 / 1000) (9791 / 200) (-552091 / 1000) (50199 / 125000) (11877 / 4) (1988821 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (922687 / 250000) (64359753447 / 1000000) (1988821 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922687 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922687 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell222 :
    ∀ t ∈ Set.Icc ((41251 / 512000) : ℝ) (41253 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174845581 / 1000000000) : ℝ) ≤ Real.exp (2 * (41251 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41251 / 512000)) (1174845581 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41253 / 512000) : ℝ)) ≤ (29371369 / 25000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41253 / 512000)) (29371369 / 25000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32182676493 / 500000) : ℝ) ≤ Real.exp (3 * (3690777 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3690777 / 1000000)) (32182676493 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41251 / 512000) : ℝ) (41253 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3690777 / 1000000) (922731 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41251 / 512000) (41253 / 512000) (1174845581 / 1000000000) (29371369 / 25000000) (3690777 / 1000000) (922731 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41251 / 512000) (41253 / 512000) (3690777 / 1000000) (922731 / 250000) (32341 / 1000) (8087 / 250)
    (391 / 8) (48959 / 1000) (-69012 / 125) (200783 / 500000) (371168 / 125) (248581 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3690777 / 1000000) (32182676493 / 500000) (248581 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690777 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690777 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell223 :
    ∀ t ∈ Set.Icc ((41253 / 512000) : ℝ) (8251 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174854759 / 1000000000) : ℝ) ≤ Real.exp (2 * (41253 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41253 / 512000)) (1174854759 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8251 / 102400) : ℝ)) ≤ (1174863939 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8251 / 102400)) (1174863939 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64370953013 / 1000000) : ℝ) ≤ Real.exp (3 * (1845403 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1845403 / 500000)) (64370953013 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41253 / 512000) : ℝ) (8251 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1845403 / 500000) (3690953 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41253 / 512000) (8251 / 102400) (1174854759 / 1000000000) (1174863939 / 1000000000) (1845403 / 500000) (3690953 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41253 / 512000) (8251 / 102400) (1845403 / 500000) (3690953 / 1000000) (16171 / 500) (8087 / 250)
    (24439 / 500) (24481 / 500) (-552101 / 1000) (401541 / 1000000) (2969437 / 1000) (79539 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1845403 / 500000) (64370953013 / 1000000) (79539 / 20000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1845403 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1845403 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell224 :
    ∀ t ∈ Set.Icc ((8251 / 102400) : ℝ) (41257 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587431969 / 500000000) : ℝ) ≤ Real.exp (2 * (8251 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8251 / 102400)) (587431969 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41257 / 512000) : ℝ)) ≤ (587436559 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41257 / 512000)) (587436559 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64376553527 / 1000000) : ℝ) ≤ Real.exp (3 * (738167 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (738167 / 200000)) (64376553527 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8251 / 102400) : ℝ) (41257 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (738167 / 200000) (1845491 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8251 / 102400) (41257 / 512000) (587431969 / 500000000) (587436559 / 500000000) (738167 / 200000) (1845491 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8251 / 102400) (41257 / 512000) (738167 / 200000) (1845491 / 500000) (32343 / 1000) (32349 / 1000)
    (24441 / 500) (24483 / 500) (-276053 / 500) (100379 / 250000) (296953 / 100) (994151 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (738167 / 200000) (64376553527 / 1000000) (994151 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (738167 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (738167 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell225 :
    ∀ t ∈ Set.Icc ((41257 / 512000) : ℝ) (41259 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174873117 / 1000000000) : ℝ) ≤ Real.exp (2 * (41257 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41257 / 512000)) (1174873117 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41259 / 512000) : ℝ)) ≤ (146860287 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41259 / 512000)) (146860287 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32190980691 / 500000) : ℝ) ≤ Real.exp (3 * (3690863 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3690863 / 1000000)) (32190980691 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41257 / 512000) : ℝ) (41259 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3690863 / 1000000) (3691011 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41257 / 512000) (41259 / 512000) (1174873117 / 1000000000) (146860287 / 125000000) (3690863 / 1000000) (3691011 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41257 / 512000) (41259 / 512000) (3690863 / 1000000) (3691011 / 1000000) (32343 / 1000) (647 / 20)
    (9777 / 200) (48969 / 1000) (-552107 / 1000) (401491 / 1000000) (371203 / 125) (397627 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3690863 / 1000000) (32190980691 / 500000) (397627 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690863 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690863 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell226 :
    ∀ t ∈ Set.Icc ((41259 / 512000) : ℝ) (41261 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((234976459 / 200000000) : ℝ) ≤ Real.exp (2 * (41259 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41259 / 512000)) (234976459 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41261 / 512000) : ℝ)) ≤ (46995659 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41261 / 512000)) (46995659 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32193781427 / 500000) : ℝ) ≤ Real.exp (3 * (922723 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (922723 / 250000)) (32193781427 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41259 / 512000) : ℝ) (41261 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (922723 / 250000) (23069 / 6250) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41259 / 512000) (41261 / 512000) (234976459 / 200000000) (46995659 / 40000000) (922723 / 250000) (23069 / 6250) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41259 / 512000) (41261 / 512000) (922723 / 250000) (23069 / 6250) (4043 / 125) (647 / 20)
    (6111 / 125) (48973 / 1000) (-69014 / 125) (200733 / 500000) (2969717 / 1000) (993981 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (922723 / 250000) (32193781427 / 500000) (993981 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922723 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922723 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell227 :
    ∀ t ∈ Set.Icc ((41261 / 512000) : ℝ) (41263 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587445737 / 500000000) : ℝ) ≤ Real.exp (2 * (41261 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41261 / 512000)) (587445737 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41263 / 512000) : ℝ)) ≤ (587450327 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41263 / 512000)) (587450327 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64393164813 / 1000000) : ℝ) ≤ Real.exp (3 * (3690921 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3690921 / 1000000)) (64393164813 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41261 / 512000) : ℝ) (41263 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3690921 / 1000000) (922767 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41261 / 512000) (41263 / 512000) (587445737 / 500000000) (587450327 / 500000000) (3690921 / 1000000) (922767 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41261 / 512000) (41263 / 512000) (3690921 / 1000000) (922767 / 250000) (6469 / 200) (32351 / 1000)
    (12223 / 250) (6122 / 125) (-276061 / 500) (2509 / 6250) (2969807 / 1000) (1987789 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3690921 / 1000000) (64393164813 / 1000000) (1987789 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690921 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690921 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell228 :
    ∀ t ∈ Set.Icc ((41263 / 512000) : ℝ) (8253 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174900653 / 1000000000) : ℝ) ≤ Real.exp (2 * (41263 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41263 / 512000)) (1174900653 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8253 / 102400) : ℝ)) ≤ (1174909833 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8253 / 102400)) (1174909833 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3219938363 / 50000) : ℝ) ≤ Real.exp (3 * (73819 / 20000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (73819 / 20000)) (3219938363 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41263 / 512000) : ℝ) (8253 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (73819 / 20000) (3691097 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41263 / 512000) (8253 / 102400) (1174900653 / 1000000000) (1174909833 / 1000000000) (73819 / 20000) (3691097 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41263 / 512000) (8253 / 102400) (73819 / 20000) (3691097 / 1000000) (6469 / 200) (4044 / 125)
    (6112 / 125) (48979 / 1000) (-552127 / 1000) (80283 / 200000) (29699 / 10) (62113 / 15625000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (73819 / 20000) (3219938363 / 50000) (62113 / 15625000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (73819 / 20000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (73819 / 20000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell229 :
    ∀ t ∈ Set.Icc ((8253 / 102400) : ℝ) (41267 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((146863729 / 125000000) : ℝ) ≤ Real.exp (2 * (8253 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8253 / 102400)) (146863729 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41267 / 512000) : ℝ)) ≤ (293729753 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41267 / 512000)) (293729753 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32202185097 / 500000) : ℝ) ≤ Real.exp (3 * (3690979 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3690979 / 1000000)) (32202185097 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8253 / 102400) : ℝ) (41267 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3690979 / 1000000) (1845563 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8253 / 102400) (41267 / 512000) (146863729 / 125000000) (293729753 / 250000000) (3690979 / 1000000) (1845563 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8253 / 102400) (41267 / 512000) (3690979 / 1000000) (1845563 / 500000) (16173 / 500) (4044 / 125)
    (48899 / 1000) (48983 / 1000) (-138033 / 250) (401389 / 1000000) (1484997 / 500) (1987443 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3690979 / 1000000) (32202185097 / 500000) (1987443 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690979 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690979 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell230 :
    ∀ t ∈ Set.Icc ((41267 / 512000) : ℝ) (41269 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174919011 / 1000000000) : ℝ) ≤ Real.exp (2 * (41267 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41267 / 512000)) (1174919011 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41269 / 512000) : ℝ)) ≤ (1174928191 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41269 / 512000)) (1174928191 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((12881994723 / 200000) : ℝ) ≤ Real.exp (3 * (57672 / 15625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (57672 / 15625)) (12881994723 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41267 / 512000) : ℝ) (41269 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (57672 / 15625) (738231 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41267 / 512000) (41269 / 512000) (1174919011 / 1000000000) (1174928191 / 1000000000) (57672 / 15625) (738231 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41267 / 512000) (41269 / 512000) (57672 / 15625) (738231 / 200000) (32347 / 1000) (32353 / 1000)
    (48903 / 1000) (24493 / 500) (-552137 / 1000) (100341 / 250000) (2970087 / 1000) (198727 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (57672 / 15625) (12881994723 / 200000) (198727 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (57672 / 15625)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (57672 / 15625)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell231 :
    ∀ t ∈ Set.Icc ((41269 / 512000) : ℝ) (41271 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((117492819 / 100000000) : ℝ) ≤ Real.exp (2 * (41269 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41269 / 512000)) (117492819 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41271 / 512000) : ℝ)) ≤ (117493737 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41271 / 512000)) (117493737 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32207692139 / 500000) : ℝ) ≤ Real.exp (3 * (922759 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (922759 / 250000)) (32207692139 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41269 / 512000) : ℝ) (41271 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (922759 / 250000) (230699 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41269 / 512000) (41271 / 512000) (117492819 / 100000000) (117493737 / 100000000) (922759 / 250000) (230699 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41269 / 512000) (41271 / 512000) (922759 / 250000) (230699 / 62500) (32347 / 1000) (16177 / 500)
    (24453 / 500) (4899 / 100) (-276069 / 500) (401339 / 1000000) (148509 / 50) (1987103 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (922759 / 250000) (32207692139 / 500000) (1987103 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922759 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922759 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell232 :
    ∀ t ∈ Set.Icc ((41271 / 512000) : ℝ) (41273 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174937369 / 1000000000) : ℝ) ≤ Real.exp (2 * (41271 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41271 / 512000)) (1174937369 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41273 / 512000) : ℝ)) ≤ (1174946549 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41273 / 512000)) (1174946549 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32210494329 / 500000) : ℝ) ≤ Real.exp (3 * (738213 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (738213 / 200000)) (32210494329 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41271 / 512000) : ℝ) (41273 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (738213 / 200000) (3691213 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41271 / 512000) (41273 / 512000) (1174937369 / 1000000000) (1174946549 / 1000000000) (738213 / 200000) (3691213 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41271 / 512000) (41273 / 512000) (738213 / 200000) (3691213 / 1000000) (8087 / 250) (16177 / 500)
    (48909 / 1000) (24497 / 500) (-552143 / 1000) (200657 / 500000) (1485137 / 500) (3973861 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (738213 / 200000) (32210494329 / 500000) (3973861 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (738213 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (738213 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell233 :
    ∀ t ∈ Set.Icc ((41273 / 512000) : ℝ) (1651 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293736637 / 250000000) : ℝ) ≤ Real.exp (2 * (41273 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41273 / 512000)) (293736637 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1651 / 20480) : ℝ)) ≤ (1174955729 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1651 / 20480)) (1174955729 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2577063741 / 40000) : ℝ) ≤ Real.exp (3 * (1845547 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1845547 / 500000)) (2577063741 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41273 / 512000) : ℝ) (1651 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1845547 / 500000) (3691241 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41273 / 512000) (1651 / 20480) (293736637 / 250000000) (1174955729 / 1000000000) (1845547 / 500000) (3691241 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41273 / 512000) (1651 / 20480) (1845547 / 500000) (3691241 / 1000000) (32349 / 1000) (6471 / 200)
    (48913 / 1000) (48997 / 1000) (-552153 / 1000) (50161 / 125000) (742591 / 250) (794703 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1845547 / 500000) (2577063741 / 40000) (794703 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1845547 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1845547 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell234 :
    ∀ t ∈ Set.Icc ((1651 / 20480) : ℝ) (41277 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((73434733 / 62500000) : ℝ) ≤ Real.exp (2 * (1651 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1651 / 20480)) (73434733 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41277 / 512000) : ℝ)) ≤ (293741227 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41277 / 512000)) (293741227 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((402701243 / 6250) : ℝ) ≤ Real.exp (3 * (3691123 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3691123 / 1000000)) (402701243 / 6250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1651 / 20480) : ℝ) (41277 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3691123 / 1000000) (369127 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1651 / 20480) (41277 / 512000) (73434733 / 62500000) (293741227 / 250000000) (3691123 / 1000000) (369127 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1651 / 20480) (41277 / 512000) (3691123 / 1000000) (369127 / 100000) (32349 / 1000) (8089 / 250)
    (12229 / 250) (49) (-276079 / 500) (401263 / 1000000) (2970457 / 1000) (3973169 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3691123 / 1000000) (402701243 / 6250) (3973169 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3691123 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3691123 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell235 :
    ∀ t ∈ Set.Icc ((41277 / 512000) : ℝ) (41279 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174964907 / 1000000000) : ℝ) ≤ Real.exp (2 * (41277 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41277 / 512000)) (1174964907 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41279 / 512000) : ℝ)) ≤ (146871761 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41279 / 512000)) (146871761 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64437804723 / 1000000) : ℝ) ≤ Real.exp (3 * (230697 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (230697 / 62500)) (64437804723 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41277 / 512000) : ℝ) (41279 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (230697 / 62500) (3691299 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41277 / 512000) (41279 / 512000) (1174964907 / 1000000000) (146871761 / 125000000) (230697 / 62500) (3691299 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41277 / 512000) (41279 / 512000) (230697 / 62500) (3691299 / 1000000) (647 / 20) (8089 / 250)
    (1223 / 25) (12251 / 250) (-552163 / 1000) (401237 / 1000000) (2970551 / 1000) (496603 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (230697 / 62500) (64437804723 / 1000000) (496603 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (230697 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (230697 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell236 :
    ∀ t ∈ Set.Icc ((41279 / 512000) : ℝ) (41281 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174974087 / 1000000000) : ℝ) ≤ Real.exp (2 * (41279 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41279 / 512000)) (1174974087 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41281 / 512000) : ℝ)) ≤ (1174983267 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41281 / 512000)) (1174983267 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64443411053 / 1000000) : ℝ) ≤ Real.exp (3 * (3691181 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3691181 / 1000000)) (64443411053 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41279 / 512000) : ℝ) (41281 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3691181 / 1000000) (57677 / 15625) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41279 / 512000) (41281 / 512000) (1174974087 / 1000000000) (1174983267 / 1000000000) (3691181 / 1000000) (57677 / 15625) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41279 / 512000) (41281 / 512000) (3691181 / 1000000) (57677 / 15625) (32351 / 1000) (32357 / 1000)
    (48923 / 1000) (49007 / 1000) (-69021 / 125) (100303 / 250000) (742661 / 250) (1986239 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3691181 / 1000000) (64443411053 / 1000000) (1986239 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3691181 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3691181 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell237 :
    ∀ t ∈ Set.Icc ((41281 / 512000) : ℝ) (41283 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587491633 / 500000000) : ℝ) ≤ Real.exp (2 * (41281 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41281 / 512000)) (587491633 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41283 / 512000) : ℝ)) ≤ (1174992447 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41283 / 512000)) (1174992447 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2577952981 / 40000) : ℝ) ≤ Real.exp (3 * (3691209 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3691209 / 1000000)) (2577952981 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41281 / 512000) : ℝ) (41283 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3691209 / 1000000) (3691357 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41281 / 512000) (41283 / 512000) (587491633 / 500000000) (1174992447 / 1000000000) (3691209 / 1000000) (3691357 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41281 / 512000) (41283 / 512000) (3691209 / 1000000) (3691357 / 1000000) (32351 / 1000) (16179 / 500)
    (48927 / 1000) (49011 / 1000) (-552169 / 1000) (401187 / 1000000) (2970737 / 1000) (248259 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3691209 / 1000000) (2577952981 / 40000) (248259 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3691209 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3691209 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell238 :
    ∀ t ∈ Set.Icc ((41283 / 512000) : ℝ) (8257 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587496223 / 500000000) : ℝ) ≤ Real.exp (2 * (41283 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41283 / 512000)) (587496223 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8257 / 102400) : ℝ)) ≤ (587500813 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8257 / 102400)) (587500813 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32227215907 / 500000) : ℝ) ≤ Real.exp (3 * (1845619 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1845619 / 500000)) (32227215907 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41283 / 512000) : ℝ) (8257 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1845619 / 500000) (1845693 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41283 / 512000) (8257 / 102400) (587496223 / 500000000) (587500813 / 500000000) (1845619 / 500000) (1845693 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41283 / 512000) (8257 / 102400) (1845619 / 500000) (1845693 / 500000) (4044 / 125) (16179 / 500)
    (4893 / 100) (9803 / 200) (-276087 / 500) (200581 / 500000) (2970831 / 1000) (3971799 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1845619 / 500000) (32227215907 / 500000) (3971799 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1845619 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1845619 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell239 :
    ∀ t ∈ Set.Icc ((8257 / 102400) : ℝ) (41287 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((9400013 / 8000000) : ℝ) ≤ Real.exp (2 * (8257 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8257 / 102400)) (9400013 / 8000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41287 / 512000) : ℝ)) ≤ (587505403 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41287 / 512000)) (587505403 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64460039591 / 1000000) : ℝ) ≤ Real.exp (3 * (3691267 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3691267 / 1000000)) (64460039591 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8257 / 102400) : ℝ) (41287 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3691267 / 1000000) (1845707 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8257 / 102400) (41287 / 512000) (9400013 / 8000000) (587505403 / 500000000) (3691267 / 1000000) (1845707 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8257 / 102400) (41287 / 512000) (3691267 / 1000000) (1845707 / 500000) (32353 / 1000) (32359 / 1000)
    (24467 / 500) (24509 / 500) (-552183 / 1000) (25071 / 62500) (2970921 / 1000) (3971453 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3691267 / 1000000) (64460039591 / 1000000) (3971453 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3691267 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3691267 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch011 :
    ∀ t ∈ Set.Icc ((41247 / 512000) : ℝ) (41287 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell220
      hpThetaDensityLowerExpCompact_cell221)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell222
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell223
      hpThetaDensityLowerExpCompact_cell224)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell225
      hpThetaDensityLowerExpCompact_cell226)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell227
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell228
      hpThetaDensityLowerExpCompact_cell229))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell230
      hpThetaDensityLowerExpCompact_cell231)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell232
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell233
      hpThetaDensityLowerExpCompact_cell234)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell235
      hpThetaDensityLowerExpCompact_cell236)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell237
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell238
      hpThetaDensityLowerExpCompact_cell239)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch011
end HodgeProofHP
