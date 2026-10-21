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
theorem hpThetaDensityLowerExpCompact_cell460 :
    ∀ t ∈ Set.Icc ((41979 / 512000) : ℝ) (41983 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1178191303 / 1000000000) : ℝ) ≤ Real.exp (2 * (41979 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41979 / 512000)) (1178191303 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41983 / 512000) : ℝ)) ≤ (1178209713 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41983 / 512000)) (1178209713 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66427124649 / 1000000) : ℝ) ≤ Real.exp (3 * (3701287 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3701287 / 1000000)) (66427124649 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41979 / 512000) : ℝ) (41983 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3701287 / 1000000) (462683 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41979 / 512000) (41983 / 512000) (1178191303 / 1000000000) (1178209713 / 1000000000) (3701287 / 1000000) (462683 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41979 / 512000) (41983 / 512000) (3701287 / 1000000) (462683 / 125000) (32589 / 1000) (8149 / 250)
    (50141 / 1000) (25121 / 500) (-138453 / 250) (196223 / 500000) (3003407 / 1000) (481731 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3701287 / 1000000) (66427124649 / 1000000) (481731 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3701287 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3701287 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell461 :
    ∀ t ∈ Set.Icc ((41983 / 512000) : ℝ) (41987 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((73638107 / 62500000) : ℝ) ≤ Real.exp (2 * (41983 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41983 / 512000)) (73638107 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41987 / 512000) : ℝ)) ≤ (1178228123 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41987 / 512000)) (1178228123 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66438683969 / 1000000) : ℝ) ≤ Real.exp (3 * (740269 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (740269 / 200000)) (66438683969 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41983 / 512000) : ℝ) (41987 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (740269 / 200000) (1850761 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41983 / 512000) (41987 / 512000) (73638107 / 62500000) (1178228123 / 1000000000) (740269 / 200000) (1850761 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41983 / 512000) (41987 / 512000) (740269 / 200000) (1850761 / 500000) (3259 / 100) (32597 / 1000)
    (12537 / 250) (50249 / 1000) (-276911 / 500) (98099 / 250000) (600719 / 200) (3853177 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (740269 / 200000) (66438683969 / 1000000) (3853177 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (740269 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (740269 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell462 :
    ∀ t ∈ Set.Icc ((41987 / 512000) : ℝ) (41991 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((589114061 / 500000000) : ℝ) ≤ Real.exp (2 * (41987 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41987 / 512000)) (589114061 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41991 / 512000) : ℝ)) ≤ (1178246533 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41991 / 512000)) (1178246533 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((664502453 / 10000) : ℝ) ≤ Real.exp (3 * (3701403 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3701403 / 1000000)) (664502453 / 10000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41987 / 512000) : ℝ) (41991 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3701403 / 1000000) (185079 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41987 / 512000) (41991 / 512000) (589114061 / 500000000) (1178246533 / 1000000000) (3701403 / 1000000) (185079 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41987 / 512000) (41991 / 512000) (3701403 / 1000000) (185079 / 50000) (4074 / 125) (32599 / 1000)
    (10031 / 200) (6282 / 125) (-69229 / 125) (196173 / 500000) (3003783 / 1000) (3852507 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3701403 / 1000000) (664502453 / 10000) (3852507 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3701403 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3701403 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell463 :
    ∀ t ∈ Set.Icc ((41991 / 512000) : ℝ) (8399 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((294561633 / 250000000) : ℝ) ≤ Real.exp (2 * (41991 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41991 / 512000)) (294561633 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8399 / 102400) : ℝ)) ≤ (1178264943 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8399 / 102400)) (1178264943 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66461808643 / 1000000) : ℝ) ≤ Real.exp (3 * (3701461 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3701461 / 1000000)) (66461808643 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41991 / 512000) : ℝ) (8399 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3701461 / 1000000) (1850819 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41991 / 512000) (8399 / 102400) (294561633 / 250000000) (1178264943 / 1000000000) (3701461 / 1000000) (1850819 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41991 / 512000) (8399 / 102400) (3701461 / 1000000) (1850819 / 500000) (32593 / 1000) (163 / 5)
    (25081 / 500) (50263 / 1000) (-276921 / 500) (49037 / 125000) (750993 / 250) (3851837 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3701461 / 1000000) (66461808643 / 1000000) (3851837 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3701461 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3701461 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell464 :
    ∀ t ∈ Set.Icc ((8399 / 102400) : ℝ) (41999 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((589132471 / 500000000) : ℝ) ≤ Real.exp (2 * (8399 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8399 / 102400)) (589132471 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41999 / 512000) : ℝ)) ≤ (589141677 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41999 / 512000)) (589141677 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66473373999 / 1000000) : ℝ) ≤ Real.exp (3 * (3701519 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3701519 / 1000000)) (66473373999 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8399 / 102400) : ℝ) (41999 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3701519 / 1000000) (740339 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8399 / 102400) (41999 / 512000) (589132471 / 500000000) (589141677 / 500000000) (3701519 / 1000000) (740339 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8399 / 102400) (41999 / 512000) (3701519 / 1000000) (740339 / 200000) (16297 / 500) (16301 / 500)
    (50169 / 1000) (5027 / 100) (-69232 / 125) (196123 / 500000) (3004157 / 1000) (3851167 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3701519 / 1000000) (66473373999 / 1000000) (3851167 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3701519 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3701519 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell465 :
    ∀ t ∈ Set.Icc ((41999 / 512000) : ℝ) (42003 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1178283353 / 1000000000) : ℝ) ≤ Real.exp (2 * (41999 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41999 / 512000)) (1178283353 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42003 / 512000) : ℝ)) ≤ (294575441 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42003 / 512000)) (294575441 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66484941367 / 1000000) : ℝ) ≤ Real.exp (3 * (3701577 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3701577 / 1000000)) (66484941367 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41999 / 512000) : ℝ) (42003 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3701577 / 1000000) (3701753 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41999 / 512000) (42003 / 512000) (1178283353 / 1000000000) (294575441 / 250000000) (3701577 / 1000000) (3701753 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41999 / 512000) (42003 / 512000) (3701577 / 1000000) (3701753 / 1000000) (8149 / 250) (32603 / 1000)
    (6272 / 125) (50277 / 1000) (-276933 / 500) (98049 / 250000) (600869 / 200) (15041 / 3906250)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3701577 / 1000000) (66484941367 / 1000000) (15041 / 3906250)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3701577 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3701577 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell466 :
    ∀ t ∈ Set.Icc ((42003 / 512000) : ℝ) (42007 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1178301763 / 1000000000) : ℝ) ≤ Real.exp (2 * (42003 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42003 / 512000)) (1178301763 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42007 / 512000) : ℝ)) ≤ (73645011 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42007 / 512000)) (73645011 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((33248155629 / 500000) : ℝ) ≤ Real.exp (3 * (1850817 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1850817 / 500000)) (33248155629 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42003 / 512000) : ℝ) (42007 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1850817 / 500000) (3701811 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42003 / 512000) (42007 / 512000) (1178301763 / 1000000000) (73645011 / 62500000) (1850817 / 500000) (3701811 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42003 / 512000) (42007 / 512000) (1850817 / 500000) (3701811 / 1000000) (32597 / 1000) (8151 / 250)
    (50183 / 1000) (12571 / 250) (-69234 / 125) (392147 / 1000000) (3004533 / 1000) (1924919 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1850817 / 500000) (33248155629 / 500000) (1924919 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1850817 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1850817 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell467 :
    ∀ t ∈ Set.Icc ((42007 / 512000) : ℝ) (42011 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((47132807 / 40000000) : ℝ) ≤ Real.exp (2 * (42007 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42007 / 512000)) (47132807 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42011 / 512000) : ℝ)) ≤ (1178338587 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42011 / 512000)) (1178338587 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((33253941309 / 500000) : ℝ) ≤ Real.exp (3 * (925423 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (925423 / 250000)) (33253941309 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42007 / 512000) : ℝ) (42011 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (925423 / 250000) (3701869 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42007 / 512000) (42011 / 512000) (47132807 / 40000000) (1178338587 / 1000000000) (925423 / 250000) (3701869 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42007 / 512000) (42011 / 512000) (925423 / 250000) (3701869 / 1000000) (16299 / 500) (16303 / 500)
    (5019 / 100) (50291 / 1000) (-276941 / 500) (196049 / 500000) (1502361 / 500) (240573 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (925423 / 250000) (33253941309 / 500000) (240573 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (925423 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (925423 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell468 :
    ∀ t ∈ Set.Icc ((42011 / 512000) : ℝ) (8403 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((589169293 / 500000000) : ℝ) ≤ Real.exp (2 * (42011 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42011 / 512000)) (589169293 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8403 / 102400) : ℝ)) ≤ (1178356999 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8403 / 102400)) (1178356999 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66519455991 / 1000000) : ℝ) ≤ Real.exp (3 * (14807 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (14807 / 4000)) (66519455991 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42011 / 512000) : ℝ) (8403 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (14807 / 4000) (3701927 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42011 / 512000) (8403 / 102400) (589169293 / 500000000) (1178356999 / 1000000000) (14807 / 4000) (3701927 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42011 / 512000) (8403 / 102400) (14807 / 4000) (3701927 / 1000000) (163 / 5) (32607 / 1000)
    (50197 / 1000) (25149 / 500) (-138473 / 250) (24503 / 62500) (300491 / 100) (3848499 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (14807 / 4000) (66519455991 / 1000000) (3848499 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (14807 / 4000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (14807 / 4000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell469 :
    ∀ t ∈ Set.Icc ((8403 / 102400) : ℝ) (42019 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((589178499 / 500000000) : ℝ) ≤ Real.exp (2 * (8403 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8403 / 102400)) (589178499 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42019 / 512000) : ℝ)) ≤ (1178375411 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42019 / 512000)) (1178375411 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((33265515689 / 500000) : ℝ) ≤ Real.exp (3 * (231363 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (231363 / 62500)) (33265515689 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8403 / 102400) : ℝ) (42019 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (231363 / 62500) (740397 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8403 / 102400) (42019 / 512000) (589178499 / 500000000) (1178375411 / 1000000000) (231363 / 62500) (740397 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8403 / 102400) (42019 / 512000) (231363 / 62500) (740397 / 200000) (32601 / 1000) (4076 / 125)
    (12551 / 250) (10061 / 200) (-276951 / 500) (195999 / 500000) (1502549 / 500) (3847829 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (231363 / 62500) (33265515689 / 500000) (3847829 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (231363 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (231363 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell470 :
    ∀ t ∈ Set.Icc ((42019 / 512000) : ℝ) (42023 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((117837541 / 100000000) : ℝ) ≤ Real.exp (2 * (42019 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42019 / 512000)) (117837541 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42023 / 512000) : ℝ)) ≤ (1178393823 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42023 / 512000)) (1178393823 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66542608779 / 1000000) : ℝ) ≤ Real.exp (3 * (1850933 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1850933 / 500000)) (66542608779 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42019 / 512000) : ℝ) (42023 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1850933 / 500000) (3702043 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42019 / 512000) (42023 / 512000) (117837541 / 100000000) (1178393823 / 1000000000) (1850933 / 500000) (3702043 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42019 / 512000) (42023 / 512000) (1850933 / 500000) (3702043 / 1000000) (16301 / 500) (3261 / 100)
    (50211 / 1000) (6289 / 125) (-69239 / 125) (97987 / 250000) (3005287 / 1000) (96179 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1850933 / 500000) (66542608779 / 1000000) (96179 / 25000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1850933 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1850933 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell471 :
    ∀ t ∈ Set.Icc ((42023 / 512000) : ℝ) (42027 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((589196911 / 500000000) : ℝ) ≤ Real.exp (2 * (42023 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42023 / 512000)) (589196911 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42027 / 512000) : ℝ)) ≤ (235682447 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42027 / 512000)) (235682447 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13310837639 / 200000) : ℝ) ≤ Real.exp (3 * (925481 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (925481 / 250000)) (13310837639 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42023 / 512000) : ℝ) (42027 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (925481 / 250000) (37021 / 10000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42023 / 512000) (42027 / 512000) (589196911 / 500000000) (235682447 / 200000000) (925481 / 250000) (37021 / 10000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42023 / 512000) (42027 / 512000) (925481 / 250000) (37021 / 10000) (8151 / 250) (32611 / 1000)
    (50219 / 1000) (50319 / 1000) (-276963 / 500) (195949 / 500000) (375684 / 125) (384649 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (925481 / 250000) (13310837639 / 200000) (384649 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (925481 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (925481 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell472 :
    ∀ t ∈ Set.Icc ((42027 / 512000) : ℝ) (42031 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((589206117 / 500000000) : ℝ) ≤ Real.exp (2 * (42027 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42027 / 512000)) (589206117 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42031 / 512000) : ℝ)) ≤ (147303831 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42031 / 512000)) (147303831 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((33282884813 / 500000) : ℝ) ≤ Real.exp (3 * (1850991 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1850991 / 500000)) (33282884813 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42027 / 512000) : ℝ) (42031 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1850991 / 500000) (1851079 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42027 / 512000) (42031 / 512000) (589206117 / 500000000) (147303831 / 125000000) (1850991 / 500000) (1851079 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42027 / 512000) (42031 / 512000) (1850991 / 500000) (1851079 / 500000) (6521 / 200) (32613 / 1000)
    (25113 / 500) (25163 / 500) (-69242 / 125) (48981 / 125000) (150283 / 50) (3845821 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1850991 / 500000) (33282884813 / 500000) (3845821 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1850991 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1850991 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell473 :
    ∀ t ∈ Set.Icc ((42031 / 512000) : ℝ) (8407 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1178430647 / 1000000000) : ℝ) ≤ Real.exp (2 * (42031 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42031 / 512000)) (1178430647 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8407 / 102400) : ℝ)) ≤ (1178449061 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8407 / 102400)) (1178449061 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3328857667 / 50000) : ℝ) ≤ Real.exp (3 * (3702039 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3702039 / 1000000)) (3328857667 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42031 / 512000) : ℝ) (8407 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3702039 / 1000000) (462777 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42031 / 512000) (8407 / 102400) (1178430647 / 1000000000) (1178449061 / 1000000000) (3702039 / 1000000) (462777 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42031 / 512000) (8407 / 102400) (3702039 / 1000000) (462777 / 125000) (32607 / 1000) (16307 / 500)
    (6279 / 125) (50333 / 1000) (-276971 / 500) (1959 / 5000) (375731 / 125) (3845163 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3702039 / 1000000) (3328857667 / 50000) (3845163 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3702039 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3702039 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell474 :
    ∀ t ∈ Set.Icc ((8407 / 102400) : ℝ) (42039 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((58922453 / 50000000) : ℝ) ≤ Real.exp (2 * (8407 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8407 / 102400)) (58922453 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42039 / 512000) : ℝ)) ≤ (47138699 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42039 / 512000)) (47138699 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66588738767 / 1000000) : ℝ) ≤ Real.exp (3 * (3702097 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3702097 / 1000000)) (66588738767 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8407 / 102400) : ℝ) (42039 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3702097 / 1000000) (1851137 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8407 / 102400) (42039 / 512000) (58922453 / 50000000) (47138699 / 40000000) (3702097 / 1000000) (1851137 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8407 / 102400) (42039 / 512000) (3702097 / 1000000) (1851137 / 500000) (4076 / 125) (6523 / 200)
    (50239 / 1000) (50341 / 1000) (-69244 / 125) (1567 / 4000) (3006037 / 1000) (1922247 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3702097 / 1000000) (66588738767 / 1000000) (1922247 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3702097 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3702097 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell475 :
    ∀ t ∈ Set.Icc ((42039 / 512000) : ℝ) (42043 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((589233737 / 500000000) : ℝ) ≤ Real.exp (2 * (42039 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42039 / 512000)) (589233737 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42043 / 512000) : ℝ)) ≤ (9206921 / 7812500) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42043 / 512000)) (9206921 / 7812500) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6660032621 / 100000) : ℝ) ≤ Real.exp (3 * (740431 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (740431 / 200000)) (6660032621 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42039 / 512000) : ℝ) (42043 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (740431 / 200000) (925583 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42039 / 512000) (42043 / 512000) (589233737 / 500000000) (9206921 / 7812500) (740431 / 200000) (925583 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42039 / 512000) (42043 / 512000) (740431 / 200000) (925583 / 250000) (32609 / 1000) (32617 / 1000)
    (25123 / 500) (12587 / 250) (-276981 / 500) (3917 / 10000) (120249 / 40) (1921913 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (740431 / 200000) (6660032621 / 100000) (1921913 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (740431 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (740431 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell476 :
    ∀ t ∈ Set.Icc ((42043 / 512000) : ℝ) (42047 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1178485887 / 1000000000) : ℝ) ≤ Real.exp (2 * (42043 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42043 / 512000)) (1178485887 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42047 / 512000) : ℝ)) ≤ (589252151 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42047 / 512000)) (589252151 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6661191567 / 100000) : ℝ) ≤ Real.exp (3 * (3702213 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3702213 / 1000000)) (6661191567 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42043 / 512000) : ℝ) (42047 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3702213 / 1000000) (370239 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42043 / 512000) (42047 / 512000) (1178485887 / 1000000000) (589252151 / 500000000) (3702213 / 1000000) (370239 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42043 / 512000) (42047 / 512000) (3702213 / 1000000) (370239 / 100000) (32611 / 1000) (16309 / 500)
    (50253 / 1000) (10071 / 200) (-138493 / 250) (391651 / 1000000) (3006413 / 1000) (3843157 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3702213 / 1000000) (6661191567 / 100000) (3843157 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3702213 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3702213 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell477 :
    ∀ t ∈ Set.Icc ((42047 / 512000) : ℝ) (42051 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1178504301 / 1000000000) : ℝ) ≤ Real.exp (2 * (42047 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42047 / 512000)) (1178504301 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42051 / 512000) : ℝ)) ≤ (1178522717 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42051 / 512000)) (1178522717 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((33311753573 / 500000) : ℝ) ≤ Real.exp (3 * (3702271 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3702271 / 1000000)) (33311753573 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42047 / 512000) : ℝ) (42051 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3702271 / 1000000) (3702447 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42047 / 512000) (42051 / 512000) (1178504301 / 1000000000) (1178522717 / 1000000000) (3702271 / 1000000) (3702447 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42047 / 512000) (42051 / 512000) (3702271 / 1000000) (3702447 / 1000000) (8153 / 250) (32619 / 1000)
    (50261 / 1000) (50361 / 1000) (-276993 / 500) (391601 / 1000000) (3006599 / 1000) (480311 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3702271 / 1000000) (33311753573 / 500000) (480311 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3702271 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3702271 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell478 :
    ∀ t ∈ Set.Icc ((42051 / 512000) : ℝ) (8411 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((294630679 / 250000000) : ℝ) ≤ Real.exp (2 * (42051 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42051 / 512000)) (294630679 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8411 / 102400) : ℝ)) ≤ (1178541131 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8411 / 102400)) (1178541131 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((416469379 / 6250) : ℝ) ≤ Real.exp (3 * (3702329 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3702329 / 1000000)) (416469379 / 6250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42051 / 512000) : ℝ) (8411 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3702329 / 1000000) (740501 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42051 / 512000) (8411 / 102400) (294630679 / 250000000) (1178541131 / 1000000000) (3702329 / 1000000) (740501 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42051 / 512000) (8411 / 102400) (3702329 / 1000000) (740501 / 200000) (32613 / 1000) (32621 / 1000)
    (12567 / 250) (6296 / 125) (-138499 / 250) (391551 / 1000000) (3006787 / 1000) (192091 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3702329 / 1000000) (416469379 / 6250) (192091 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3702329 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3702329 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell479 :
    ∀ t ∈ Set.Icc ((8411 / 102400) : ℝ) (42059 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((117854113 / 100000000) : ℝ) ≤ Real.exp (2 * (8411 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8411 / 102400)) (117854113 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42059 / 512000) : ℝ)) ≤ (589279773 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42059 / 512000)) (589279773 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66646496211 / 1000000) : ℝ) ≤ Real.exp (3 * (1851193 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1851193 / 500000)) (66646496211 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8411 / 102400) : ℝ) (42059 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1851193 / 500000) (3702563 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8411 / 102400) (42059 / 512000) (117854113 / 100000000) (589279773 / 500000000) (1851193 / 500000) (3702563 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8411 / 102400) (42059 / 512000) (1851193 / 500000) (3702563 / 1000000) (6523 / 200) (16311 / 500)
    (2011 / 40) (6297 / 125) (-277001 / 500) (195751 / 500000) (120279 / 40) (3841163 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1851193 / 500000) (66646496211 / 1000000) (3841163 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1851193 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1851193 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch023 :
    ∀ t ∈ Set.Icc ((41979 / 512000) : ℝ) (42059 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell460
      hpThetaDensityLowerExpCompact_cell461)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell462
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell463
      hpThetaDensityLowerExpCompact_cell464)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell465
      hpThetaDensityLowerExpCompact_cell466)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell467
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell468
      hpThetaDensityLowerExpCompact_cell469))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell470
      hpThetaDensityLowerExpCompact_cell471)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell472
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell473
      hpThetaDensityLowerExpCompact_cell474)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell475
      hpThetaDensityLowerExpCompact_cell476)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell477
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell478
      hpThetaDensityLowerExpCompact_cell479)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch023
end HodgeProofHP
