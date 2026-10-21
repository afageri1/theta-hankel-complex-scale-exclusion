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
theorem hpThetaDensityLowerExpCompact_cell280 :
    ∀ t ∈ Set.Icc ((41367 / 512000) : ℝ) (41369 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175378053 / 1000000000) : ℝ) ≤ Real.exp (2 * (41367 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41367 / 512000)) (1175378053 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41369 / 512000) : ℝ)) ≤ (1175387237 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41369 / 512000)) (1175387237 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64689214599 / 1000000) : ℝ) ≤ Real.exp (3 * (73849 / 20000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (73849 / 20000)) (64689214599 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41367 / 512000) : ℝ) (41369 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (73849 / 20000) (3692597 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41367 / 512000) (41369 / 512000) (1175378053 / 1000000000) (1175387237 / 1000000000) (73849 / 20000) (3692597 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41367 / 512000) (41369 / 512000) (73849 / 20000) (3692597 / 1000000) (32381 / 1000) (32387 / 1000)
    (49077 / 1000) (1229 / 25) (-276197 / 500) (4001 / 10000) (2974731 / 1000) (494673 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (73849 / 20000) (64689214599 / 1000000) (494673 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (73849 / 20000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (73849 / 20000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell281 :
    ∀ t ∈ Set.Icc ((41369 / 512000) : ℝ) (41371 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293846809 / 250000000) : ℝ) ≤ Real.exp (2 * (41369 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41369 / 512000)) (293846809 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41371 / 512000) : ℝ)) ≤ (58769821 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41371 / 512000)) (58769821 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64694842803 / 1000000) : ℝ) ≤ Real.exp (3 * (3692479 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3692479 / 1000000)) (64694842803 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41369 / 512000) : ℝ) (41371 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3692479 / 1000000) (1846313 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41369 / 512000) (41371 / 512000) (293846809 / 250000000) (58769821 / 50000000) (3692479 / 1000000) (1846313 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41369 / 512000) (41371 / 512000) (3692479 / 1000000) (1846313 / 500000) (32381 / 1000) (8097 / 250)
    (1227 / 25) (12291 / 250) (-552399 / 1000) (200037 / 500000) (371853 / 125) (3957039 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3692479 / 1000000) (64694842803 / 1000000) (3957039 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3692479 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3692479 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell282 :
    ∀ t ∈ Set.Icc ((41371 / 512000) : ℝ) (41373 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175396419 / 1000000000) : ℝ) ≤ Real.exp (2 * (41371 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41371 / 512000)) (1175396419 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41373 / 512000) : ℝ)) ≤ (1175405603 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41373 / 512000)) (1175405603 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16175069349 / 250000) : ℝ) ≤ Real.exp (3 * (3692507 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3692507 / 1000000)) (16175069349 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41371 / 512000) : ℝ) (41373 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3692507 / 1000000) (738531 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41371 / 512000) (41373 / 512000) (1175396419 / 1000000000) (1175405603 / 1000000000) (3692507 / 1000000) (738531 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41371 / 512000) (41373 / 512000) (3692507 / 1000000) (738531 / 200000) (16191 / 500) (8097 / 250)
    (49083 / 1000) (6146 / 125) (-2762 / 5) (8001 / 20000) (1487459 / 500) (3956707 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3692507 / 1000000) (16175069349 / 250000) (3956707 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3692507 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3692507 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell283 :
    ∀ t ∈ Set.Icc ((41373 / 512000) : ℝ) (331 / 4096), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587702801 / 500000000) : ℝ) ≤ Real.exp (2 * (41373 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41373 / 512000)) (587702801 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((331 / 4096) : ℝ)) ≤ (235082957 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (331 / 4096)) (235082957 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32352953281 / 500000) : ℝ) ≤ Real.exp (3 * (461567 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (461567 / 125000)) (32352953281 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41373 / 512000) : ℝ) (331 / 4096),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (461567 / 125000) (923171 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41373 / 512000) (331 / 4096) (587702801 / 500000000) (235082957 / 200000000) (461567 / 125000) (923171 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41373 / 512000) (331 / 4096) (461567 / 125000) (923171 / 250000) (32383 / 1000) (32389 / 1000)
    (49087 / 1000) (49171 / 1000) (-110481 / 200) (16001 / 40000) (2975011 / 1000) (3956363 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (461567 / 125000) (32352953281 / 500000) (3956363 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461567 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461567 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell284 :
    ∀ t ∈ Set.Icc ((331 / 4096) : ℝ) (41377 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2295732 / 1953125) : ℝ) ≤ Real.exp (2 * (331 / 4096)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (331 / 4096)) (2295732 / 1953125) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41377 / 512000) : ℝ)) ≤ (36731999 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41377 / 512000)) (36731999 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64711536219 / 1000000) : ℝ) ≤ Real.exp (3 * (738513 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (738513 / 200000)) (64711536219 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((331 / 4096) : ℝ) (41377 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (738513 / 200000) (461589 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (331 / 4096) (41377 / 512000) (2295732 / 1953125) (36731999 / 31250000) (738513 / 200000) (461589 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (331 / 4096) (41377 / 512000) (738513 / 200000) (461589 / 125000) (32383 / 1000) (3239 / 100)
    (4909 / 100) (24587 / 500) (-276207 / 500) (399999 / 1000000) (1487551 / 500) (1978009 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (738513 / 200000) (64711536219 / 1000000) (1978009 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (738513 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (738513 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell285 :
    ∀ t ∈ Set.Icc ((41377 / 512000) : ℝ) (41379 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175423967 / 1000000000) : ℝ) ≤ Real.exp (2 * (41377 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41377 / 512000)) (1175423967 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41379 / 512000) : ℝ)) ≤ (1175433151 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41379 / 512000)) (1175433151 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((12943433273 / 200000) : ℝ) ≤ Real.exp (3 * (1846297 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1846297 / 500000)) (12943433273 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41377 / 512000) : ℝ) (41379 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1846297 / 500000) (3692741 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41377 / 512000) (41379 / 512000) (1175423967 / 1000000000) (1175433151 / 1000000000) (1846297 / 500000) (3692741 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41377 / 512000) (41379 / 512000) (1846297 / 500000) (3692741 / 1000000) (4048 / 125) (3239 / 100)
    (24547 / 500) (24589 / 500) (-552419 / 1000) (199987 / 500000) (595039 / 200) (1977837 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1846297 / 500000) (12943433273 / 200000) (1977837 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1846297 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1846297 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell286 :
    ∀ t ∈ Set.Icc ((41379 / 512000) : ℝ) (41381 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((23508663 / 20000000) : ℝ) ≤ Real.exp (2 * (41379 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41379 / 512000)) (23508663 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41381 / 512000) : ℝ)) ≤ (235088467 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41381 / 512000)) (235088467 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64722797 / 1000) : ℝ) ≤ Real.exp (3 * (3692623 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3692623 / 1000000)) (64722797 / 1000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41379 / 512000) : ℝ) (41381 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3692623 / 1000000) (369277 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41379 / 512000) (41381 / 512000) (23508663 / 20000000) (235088467 / 200000000) (3692623 / 1000000) (369277 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41379 / 512000) (41381 / 512000) (3692623 / 1000000) (369277 / 100000) (6477 / 200) (32391 / 1000)
    (49097 / 1000) (49181 / 1000) (-22097 / 40) (99987 / 250000) (2975289 / 1000) (395533 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3692623 / 1000000) (64722797 / 1000) (395533 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3692623 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3692623 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell287 :
    ∀ t ∈ Set.Icc ((41381 / 512000) : ℝ) (41383 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587721167 / 500000000) : ℝ) ≤ Real.exp (2 * (41381 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41381 / 512000)) (587721167 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41383 / 512000) : ℝ)) ≤ (587725759 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41383 / 512000)) (587725759 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32364214063 / 500000) : ℝ) ≤ Real.exp (3 * (923163 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (923163 / 250000)) (32364214063 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41381 / 512000) : ℝ) (41383 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (923163 / 250000) (3692799 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41381 / 512000) (41383 / 512000) (587721167 / 500000000) (587725759 / 500000000) (923163 / 250000) (3692799 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41381 / 512000) (41383 / 512000) (923163 / 250000) (3692799 / 1000000) (6477 / 200) (4049 / 125)
    (49101 / 1000) (9837 / 200) (-55243 / 100) (399923 / 1000000) (1487691 / 500) (1977493 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (923163 / 250000) (32364214063 / 500000) (1977493 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (923163 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (923163 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell288 :
    ∀ t ∈ Set.Icc ((41383 / 512000) : ℝ) (8277 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175451517 / 1000000000) : ℝ) ≤ Real.exp (2 * (41383 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41383 / 512000)) (1175451517 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8277 / 102400) : ℝ)) ≤ (1175460701 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8277 / 102400)) (1175460701 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3236693277 / 50000) : ℝ) ≤ Real.exp (3 * (92317 / 25000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (92317 / 25000)) (3236693277 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41383 / 512000) : ℝ) (8277 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (92317 / 25000) (923207 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41383 / 512000) (8277 / 102400) (1175451517 / 1000000000) (1175460701 / 1000000000) (92317 / 25000) (923207 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41383 / 512000) (8277 / 102400) (92317 / 25000) (923207 / 250000) (16193 / 500) (4049 / 125)
    (6138 / 125) (12297 / 250) (-55243 / 100) (399899 / 1000000) (119019 / 40) (1977327 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (92317 / 25000) (3236693277 / 50000) (1977327 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (92317 / 25000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (92317 / 25000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell289 :
    ∀ t ∈ Set.Icc ((8277 / 102400) : ℝ) (41387 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((11754607 / 10000000) : ℝ) ≤ Real.exp (2 * (8277 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8277 / 102400)) (11754607 / 10000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41387 / 512000) : ℝ)) ≤ (293867471 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41387 / 512000)) (293867471 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64739497629 / 1000000) : ℝ) ≤ Real.exp (3 * (3692709 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3692709 / 1000000)) (64739497629 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8277 / 102400) : ℝ) (41387 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3692709 / 1000000) (3692857 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8277 / 102400) (41387 / 512000) (11754607 / 10000000) (293867471 / 250000000) (3692709 / 1000000) (3692857 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8277 / 102400) (41387 / 512000) (3692709 / 1000000) (3692857 / 1000000) (32387 / 1000) (32393 / 1000)
    (12277 / 250) (6149 / 125) (-110487 / 200) (399873 / 1000000) (2975569 / 1000) (395431 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3692709 / 1000000) (64739497629 / 1000000) (395431 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3692709 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3692709 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell290 :
    ∀ t ∈ Set.Icc ((41387 / 512000) : ℝ) (41389 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175469883 / 1000000000) : ℝ) ≤ Real.exp (2 * (41387 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41387 / 512000)) (1175469883 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41389 / 512000) : ℝ)) ≤ (293869767 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41389 / 512000)) (293869767 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2023285319 / 31250) : ℝ) ≤ Real.exp (3 * (1846369 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1846369 / 500000)) (2023285319 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41387 / 512000) : ℝ) (41389 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1846369 / 500000) (1846443 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41387 / 512000) (41389 / 512000) (1175469883 / 1000000000) (293869767 / 250000000) (1846369 / 500000) (1846443 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41387 / 512000) (41389 / 512000) (1846369 / 500000) (1846443 / 500000) (32387 / 1000) (16197 / 500)
    (49111 / 1000) (9839 / 200) (-552441 / 1000) (49981 / 125000) (1487831 / 500) (1976983 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1846369 / 500000) (2023285319 / 31250) (1976983 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1846369 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1846369 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell291 :
    ∀ t ∈ Set.Icc ((41389 / 512000) : ℝ) (41391 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175479067 / 1000000000) : ℝ) ≤ Real.exp (2 * (41389 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41389 / 512000)) (1175479067 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41391 / 512000) : ℝ)) ≤ (1175488251 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41391 / 512000)) (1175488251 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16187690819 / 250000) : ℝ) ≤ Real.exp (3 * (3692767 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3692767 / 1000000)) (16187690819 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41389 / 512000) : ℝ) (41391 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3692767 / 1000000) (1846457 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41389 / 512000) (41391 / 512000) (1175479067 / 1000000000) (1175488251 / 1000000000) (3692767 / 1000000) (1846457 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41389 / 512000) (41391 / 512000) (3692767 / 1000000) (1846457 / 500000) (8097 / 250) (16197 / 500)
    (9823 / 200) (49199 / 1000) (-11049 / 20) (199911 / 500000) (2975753 / 1000) (1976811 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3692767 / 1000000) (16187690819 / 250000) (1976811 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3692767 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3692767 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell292 :
    ∀ t ∈ Set.Icc ((41391 / 512000) : ℝ) (41393 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((4701953 / 4000000) : ℝ) ≤ Real.exp (2 * (41391 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41391 / 512000)) (4701953 / 4000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41393 / 512000) : ℝ)) ≤ (235099487 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41393 / 512000)) (235099487 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((12951279367 / 200000) : ℝ) ≤ Real.exp (3 * (923199 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (923199 / 250000)) (12951279367 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41391 / 512000) : ℝ) (41393 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (923199 / 250000) (3692943 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41391 / 512000) (41393 / 512000) (4701953 / 4000000) (235099487 / 200000000) (923199 / 250000) (3692943 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41391 / 512000) (41393 / 512000) (923199 / 250000) (3692943 / 1000000) (32389 / 1000) (6479 / 200)
    (24559 / 500) (24601 / 500) (-110491 / 200) (399797 / 1000000) (1487923 / 500) (1976639 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (923199 / 250000) (12951279367 / 200000) (1976639 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (923199 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (923199 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell293 :
    ∀ t ∈ Set.Icc ((41393 / 512000) : ℝ) (8279 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587748717 / 500000000) : ℝ) ≤ Real.exp (2 * (41393 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41393 / 512000)) (587748717 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8279 / 102400) : ℝ)) ≤ (587753309 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8279 / 102400)) (587753309 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16190507721 / 250000) : ℝ) ≤ Real.exp (3 * (147713 / 40000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (147713 / 40000)) (16190507721 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41393 / 512000) : ℝ) (8279 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (147713 / 40000) (923243 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41393 / 512000) (8279 / 102400) (587748717 / 500000000) (587753309 / 500000000) (147713 / 40000) (923243 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41393 / 512000) (8279 / 102400) (147713 / 40000) (923243 / 250000) (32389 / 1000) (8099 / 250)
    (24561 / 500) (24603 / 500) (-27623 / 50) (99943 / 250000) (148797 / 50) (1976467 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (147713 / 40000) (16190507721 / 250000) (1976467 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (147713 / 40000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (147713 / 40000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell294 :
    ∀ t ∈ Set.Icc ((8279 / 102400) : ℝ) (41397 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175506617 / 1000000000) : ℝ) ≤ Real.exp (2 * (8279 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8279 / 102400)) (1175506617 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41397 / 512000) : ℝ)) ≤ (587757901 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41397 / 512000)) (587757901 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4047979089 / 62500) : ℝ) ≤ Real.exp (3 * (1846427 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1846427 / 500000)) (4047979089 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8279 / 102400) : ℝ) (41397 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1846427 / 500000) (3693001 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8279 / 102400) (41397 / 512000) (1175506617 / 1000000000) (587757901 / 500000000) (1846427 / 500000) (3693001 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8279 / 102400) (41397 / 512000) (1846427 / 500000) (3693001 / 1000000) (3239 / 100) (8099 / 250)
    (393 / 8) (49209 / 1000) (-276233 / 500) (199873 / 500000) (2976033 / 1000) (395259 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1846427 / 500000) (4047979089 / 62500) (395259 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1846427 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1846427 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell295 :
    ∀ t ∈ Set.Icc ((41397 / 512000) : ℝ) (41399 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175515801 / 1000000000) : ℝ) ≤ Real.exp (2 * (41397 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41397 / 512000)) (1175515801 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41399 / 512000) : ℝ)) ≤ (587762493 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41399 / 512000)) (587762493 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32386553067 / 500000) : ℝ) ≤ Real.exp (3 * (1846441 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1846441 / 500000)) (32386553067 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41397 / 512000) : ℝ) (41399 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1846441 / 500000) (369303 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41397 / 512000) (41399 / 512000) (1175515801 / 1000000000) (587762493 / 500000000) (1846441 / 500000) (369303 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41397 / 512000) (41399 / 512000) (1846441 / 500000) (369303 / 100000) (32391 / 1000) (32397 / 1000)
    (6141 / 125) (49213 / 1000) (-276233 / 500) (199861 / 500000) (2976127 / 1000) (1976129 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1846441 / 500000) (32386553067 / 500000) (1976129 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1846441 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1846441 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell296 :
    ∀ t ∈ Set.Icc ((41399 / 512000) : ℝ) (41401 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235104997 / 200000000) : ℝ) ≤ Real.exp (2 * (41399 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41399 / 512000)) (235104997 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41401 / 512000) : ℝ)) ≤ (117553417 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41401 / 512000)) (117553417 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64778741637 / 1000000) : ℝ) ≤ Real.exp (3 * (3692911 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3692911 / 1000000)) (64778741637 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41399 / 512000) : ℝ) (41401 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3692911 / 1000000) (3693059 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41399 / 512000) (41401 / 512000) (235104997 / 200000000) (117553417 / 100000000) (3692911 / 1000000) (3693059 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41399 / 512000) (41401 / 512000) (3692911 / 1000000) (3693059 / 1000000) (4049 / 125) (16199 / 500)
    (12283 / 250) (6152 / 125) (-552471 / 1000) (399697 / 1000000) (148811 / 50) (1975957 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3692911 / 1000000) (64778741637 / 1000000) (1975957 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3692911 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3692911 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell297 :
    ∀ t ∈ Set.Icc ((41401 / 512000) : ℝ) (41403 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175534169 / 1000000000) : ℝ) ≤ Real.exp (2 * (41401 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41401 / 512000)) (1175534169 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41403 / 512000) : ℝ)) ≤ (1175543353 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41403 / 512000)) (1175543353 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6478437763 / 100000) : ℝ) ≤ Real.exp (3 * (184647 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (184647 / 50000)) (6478437763 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41401 / 512000) : ℝ) (41403 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (184647 / 50000) (3693087 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41401 / 512000) (41403 / 512000) (1175534169 / 1000000000) (1175543353 / 1000000000) (184647 / 50000) (3693087 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41401 / 512000) (41403 / 512000) (184647 / 50000) (3693087 / 1000000) (4049 / 125) (16199 / 500)
    (6142 / 125) (2461 / 50) (-552481 / 1000) (399671 / 1000000) (297631 / 100) (395157 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (184647 / 50000) (6478437763 / 100000) (395157 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (184647 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (184647 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell298 :
    ∀ t ∈ Set.Icc ((41403 / 512000) : ℝ) (8281 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((146942919 / 125000000) : ℝ) ≤ Real.exp (2 * (41403 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41403 / 512000)) (146942919 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8281 / 102400) : ℝ)) ≤ (1175552537 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8281 / 102400)) (1175552537 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64790014113 / 1000000) : ℝ) ≤ Real.exp (3 * (3692969 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3692969 / 1000000)) (64790014113 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41403 / 512000) : ℝ) (8281 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3692969 / 1000000) (923279 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41403 / 512000) (8281 / 102400) (146942919 / 125000000) (1175552537 / 1000000000) (3692969 / 1000000) (923279 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41403 / 512000) (8281 / 102400) (3692969 / 1000000) (923279 / 250000) (32393 / 1000) (32399 / 1000)
    (49139 / 1000) (49223 / 1000) (-276243 / 500) (199823 / 500000) (744101 / 250) (3951227 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3692969 / 1000000) (64790014113 / 1000000) (3951227 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3692969 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3692969 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell299 :
    ∀ t ∈ Set.Icc ((8281 / 102400) : ℝ) (41407 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((146944067 / 125000000) : ℝ) ≤ Real.exp (2 * (8281 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8281 / 102400)) (146944067 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41407 / 512000) : ℝ)) ≤ (1175561721 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41407 / 512000)) (1175561721 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64795651087 / 1000000) : ℝ) ≤ Real.exp (3 * (1846499 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1846499 / 500000)) (64795651087 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8281 / 102400) : ℝ) (41407 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1846499 / 500000) (738629 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8281 / 102400) (41407 / 512000) (146944067 / 125000000) (1175561721 / 1000000000) (1846499 / 500000) (738629 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8281 / 102400) (41407 / 512000) (1846499 / 500000) (738629 / 200000) (16197 / 500) (162 / 5)
    (49143 / 1000) (49227 / 1000) (-552491 / 1000) (19981 / 50000) (2976497 / 1000) (3950883 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1846499 / 500000) (64795651087 / 1000000) (3950883 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1846499 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1846499 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch014 :
    ∀ t ∈ Set.Icc ((41367 / 512000) : ℝ) (41407 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell280
      hpThetaDensityLowerExpCompact_cell281)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell282
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell283
      hpThetaDensityLowerExpCompact_cell284)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell285
      hpThetaDensityLowerExpCompact_cell286)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell287
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell288
      hpThetaDensityLowerExpCompact_cell289))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell290
      hpThetaDensityLowerExpCompact_cell291)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell292
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell293
      hpThetaDensityLowerExpCompact_cell294)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell295
      hpThetaDensityLowerExpCompact_cell296)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell297
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell298
      hpThetaDensityLowerExpCompact_cell299)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch014
end HodgeProofHP
