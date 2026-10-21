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
theorem hpThetaDensityLowerExpCompact_cell880 :
    ∀ t ∈ Set.Icc ((46867 / 512000) : ℝ) (46899 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((600451767 / 500000000) : ℝ) ≤ Real.exp (2 * (46867 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46867 / 512000)) (600451767 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46899 / 512000) : ℝ)) ≤ (1201053657 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46899 / 512000)) (1201053657 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((41141246133 / 500000) : ℝ) ≤ Real.exp (3 * (1886319 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1886319 / 500000)) (41141246133 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46867 / 512000) : ℝ) (46899 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1886319 / 500000) (3773231 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46867 / 512000) (46899 / 512000) (600451767 / 500000000) (1201053657 / 1000000000) (1886319 / 500000) (3773231 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46867 / 512000) (46899 / 512000) (1886319 / 500000) (3773231 / 1000000) (34291 / 1000) (17157 / 500)
    (7379 / 125) (59379 / 1000) (-281493 / 500) (83903 / 250000) (3243199 / 1000) (3111233 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1886319 / 500000) (41141246133 / 500000) (3111233 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1886319 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1886319 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell881 :
    ∀ t ∈ Set.Icc ((46899 / 512000) : ℝ) (46931 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((150131707 / 125000000) : ℝ) ≤ Real.exp (2 * (46899 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46899 / 512000)) (150131707 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46931 / 512000) : ℝ)) ≤ (600601899 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46931 / 512000)) (600601899 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3295963469 / 40000) : ℝ) ≤ Real.exp (3 * (377311 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (377311 / 100000)) (3295963469 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46899 / 512000) : ℝ) (46931 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (377311 / 100000) (1886851 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46899 / 512000) (46931 / 512000) (150131707 / 125000000) (600601899 / 500000000) (377311 / 100000) (1886851 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46899 / 512000) (46931 / 512000) (377311 / 100000) (1886851 / 500000) (34303 / 1000) (1373 / 40)
    (29547 / 500) (1486 / 25) (-112611 / 200) (167631 / 500000) (3244819 / 1000) (3106831 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (377311 / 100000) (3295963469 / 40000) (3106831 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (377311 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (377311 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell882 :
    ∀ t ∈ Set.Icc ((46931 / 512000) : ℝ) (46963 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1201203797 / 1000000000) : ℝ) ≤ Real.exp (2 * (46931 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46931 / 512000)) (1201203797 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46963 / 512000) : ℝ)) ≤ (600676979 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46963 / 512000)) (600676979 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1650311977 / 20000) : ℝ) ≤ Real.exp (3 * (3773581 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3773581 / 1000000)) (1650311977 / 20000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46931 / 512000) : ℝ) (46963 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3773581 / 1000000) (1887087 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46931 / 512000) (46963 / 512000) (1201203797 / 1000000000) (600676979 / 500000000) (3773581 / 1000000) (1887087 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46931 / 512000) (46963 / 512000) (3773581 / 1000000) (1887087 / 500000) (17157 / 500) (34337 / 1000)
    (11831 / 200) (29751 / 500) (-112623 / 200) (66983 / 200000) (3246443 / 1000) (775611 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3773581 / 1000000) (1650311977 / 20000) (775611 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3773581 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3773581 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell883 :
    ∀ t ∈ Set.Icc ((46963 / 512000) : ℝ) (9399 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1201353957 / 1000000000) : ℝ) ≤ Real.exp (2 * (46963 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46963 / 512000)) (1201353957 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9399 / 102400) : ℝ)) ≤ (1201504137 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9399 / 102400)) (1201504137 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((82632523621 / 1000000) : ℝ) ≤ Real.exp (3 * (3774053 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3774053 / 1000000)) (82632523621 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46963 / 512000) : ℝ) (9399 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3774053 / 1000000) (1887323 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46963 / 512000) (9399 / 102400) (1201353957 / 1000000000) (1201504137 / 1000000000) (3774053 / 1000000) (1887323 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46963 / 512000) (9399 / 102400) (3774053 / 1000000) (1887323 / 500000) (17163 / 500) (8587 / 250)
    (59217 / 1000) (14891 / 250) (-563179 / 1000) (167283 / 500000) (3248067 / 1000) (1549027 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3774053 / 1000000) (82632523621 / 1000000) (1549027 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3774053 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3774053 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell884 :
    ∀ t ∈ Set.Icc ((9399 / 102400) : ℝ) (47027 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((150188017 / 125000000) : ℝ) ≤ Real.exp (2 * (9399 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9399 / 102400)) (150188017 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((47027 / 512000) : ℝ)) ≤ (600827167 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47027 / 512000)) (600827167 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((41374807037 / 500000) : ℝ) ≤ Real.exp (3 * (150981 / 40000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (150981 / 40000)) (41374807037 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9399 / 102400) : ℝ) (47027 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (150981 / 40000) (1887559 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9399 / 102400) (47027 / 512000) (150188017 / 125000000) (600827167 / 500000000) (150981 / 40000) (1887559 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9399 / 102400) (47027 / 512000) (150981 / 40000) (1887559 / 500000) (34337 / 1000) (34359 / 1000)
    (29639 / 500) (477 / 8) (-563243 / 1000) (167109 / 500000) (812423 / 250) (3093671 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (150981 / 40000) (41374807037 / 500000) (3093671 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (150981 / 40000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (150981 / 40000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell885 :
    ∀ t ∈ Set.Icc ((47027 / 512000) : ℝ) (47059 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1201654333 / 1000000000) : ℝ) ≤ Real.exp (2 * (47027 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47027 / 512000)) (1201654333 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((47059 / 512000) : ℝ)) ≤ (24036091 / 20000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47059 / 512000)) (24036091 / 20000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((20716717611 / 250000) : ℝ) ≤ Real.exp (3 * (3774997 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3774997 / 1000000)) (20716717611 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((47027 / 512000) : ℝ) (47059 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3774997 / 1000000) (377559 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (47027 / 512000) (47059 / 512000) (1201654333 / 1000000000) (24036091 / 20000000) (3774997 / 1000000) (377559 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (47027 / 512000) (47059 / 512000) (3774997 / 1000000) (377559 / 100000) (8587 / 250) (34371 / 1000)
    (2967 / 50) (59687 / 1000) (-563307 / 1000) (33387 / 100000) (3251317 / 1000) (3089293 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3774997 / 1000000) (20716717611 / 250000) (3089293 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3774997 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3774997 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell886 :
    ∀ t ∈ Set.Icc ((47059 / 512000) : ℝ) (47091 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1201804549 / 1000000000) : ℝ) ≤ Real.exp (2 * (47059 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47059 / 512000)) (1201804549 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((47091 / 512000) : ℝ)) ≤ (240390957 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47091 / 512000)) (240390957 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((41492022007 / 500000) : ℝ) ≤ Real.exp (3 * (943867 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (943867 / 250000)) (41492022007 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((47059 / 512000) : ℝ) (47091 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (943867 / 250000) (1888031 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (47059 / 512000) (47091 / 512000) (1201804549 / 1000000000) (240390957 / 200000000) (943867 / 250000) (1888031 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (47059 / 512000) (47091 / 512000) (943867 / 250000) (1888031 / 500000) (859 / 25) (17191 / 500)
    (59401 / 1000) (59749 / 1000) (-281683 / 500) (83381 / 250000) (3252943 / 1000) (3084931 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (943867 / 250000) (41492022007 / 500000) (3084931 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (943867 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (943867 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell887 :
    ∀ t ∈ Set.Icc ((47091 / 512000) : ℝ) (47123 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((37561087 / 31250000) : ℝ) ≤ Real.exp (2 * (47091 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47091 / 512000)) (37561087 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((47123 / 512000) : ℝ)) ≤ (1202105039 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47123 / 512000)) (1202105039 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((83101632571 / 1000000) : ℝ) ≤ Real.exp (3 * (188797 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (188797 / 50000)) (83101632571 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((47091 / 512000) : ℝ) (47123 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (188797 / 50000) (1888267 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (47091 / 512000) (47123 / 512000) (37561087 / 31250000) (1202105039 / 1000000000) (188797 / 50000) (1888267 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (47091 / 512000) (47123 / 512000) (188797 / 50000) (1888267 / 500000) (34371 / 1000) (17197 / 500)
    (59463 / 1000) (59811 / 1000) (-563429 / 1000) (333177 / 1000000) (325457 / 100) (1540283 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (188797 / 50000) (83101632571 / 1000000) (1540283 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (188797 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (188797 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell888 :
    ∀ t ∈ Set.Icc ((47123 / 512000) : ℝ) (9431 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((601052519 / 500000000) : ℝ) ≤ Real.exp (2 * (47123 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47123 / 512000)) (601052519 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9431 / 102400) : ℝ)) ≤ (75140957 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9431 / 102400)) (75140957 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((10402423469 / 125000) : ℝ) ≤ Real.exp (3 * (944103 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (944103 / 250000)) (10402423469 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((47123 / 512000) : ℝ) (9431 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (944103 / 250000) (1888503 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (47123 / 512000) (9431 / 102400) (601052519 / 500000000) (75140957 / 62500000) (944103 / 250000) (1888503 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (47123 / 512000) (9431 / 102400) (944103 / 250000) (1888503 / 500000) (34383 / 1000) (6881 / 200)
    (14881 / 250) (7484 / 125) (-563493 / 1000) (33283 / 100000) (1628099 / 500) (3076207 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (944103 / 250000) (10402423469 / 125000) (3076207 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (944103 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (944103 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell889 :
    ∀ t ∈ Set.Icc ((9431 / 102400) : ℝ) (47187 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1202255311 / 1000000000) : ℝ) ≤ Real.exp (2 * (9431 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9431 / 102400)) (1202255311 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((47187 / 512000) : ℝ)) ≤ (1202405603 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47187 / 512000)) (1202405603 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((83337559803 / 1000000) : ℝ) ≤ Real.exp (3 * (755377 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (755377 / 200000)) (83337559803 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9431 / 102400) : ℝ) (47187 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (755377 / 200000) (1888739 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9431 / 102400) (47187 / 512000) (1202255311 / 1000000000) (1202405603 / 1000000000) (755377 / 200000) (1888739 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9431 / 102400) (47187 / 512000) (755377 / 200000) (1888739 / 500000) (17197 / 500) (34417 / 1000)
    (29793 / 500) (29967 / 500) (-563561 / 1000) (332483 / 1000000) (1628913 / 500) (614369 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (755377 / 200000) (83337559803 / 1000000) (614369 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (755377 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (755377 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell890 :
    ∀ t ∈ Set.Icc ((47187 / 512000) : ℝ) (47219 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((601202801 / 500000000) : ℝ) ≤ Real.exp (2 * (47187 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47187 / 512000)) (601202801 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((47219 / 512000) : ℝ)) ≤ (1202555913 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47219 / 512000)) (1202555913 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((83455649293 / 1000000) : ℝ) ≤ Real.exp (3 * (3777357 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3777357 / 1000000)) (83455649293 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((47187 / 512000) : ℝ) (47219 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3777357 / 1000000) (75559 / 20000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (47187 / 512000) (47219 / 512000) (601202801 / 500000000) (1202555913 / 1000000000) (3777357 / 1000000) (75559 / 20000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (47187 / 512000) (47219 / 512000) (3777357 / 1000000) (75559 / 20000) (17203 / 500) (8607 / 250)
    (7456 / 125) (14999 / 250) (-70453 / 125) (332137 / 1000000) (1629727 / 500) (1533749 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3777357 / 1000000) (83455649293 / 1000000) (1533749 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3777357 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3777357 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell891 :
    ∀ t ∈ Set.Icc ((47219 / 512000) : ℝ) (47251 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((150319489 / 125000000) : ℝ) ≤ Real.exp (2 * (47219 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47219 / 512000)) (150319489 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((47251 / 512000) : ℝ)) ≤ (601353121 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47251 / 512000)) (601353121 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16714781223 / 200000) : ℝ) ≤ Real.exp (3 * (3777829 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3777829 / 1000000)) (16714781223 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((47219 / 512000) : ℝ) (47251 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3777829 / 1000000) (1889211 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (47219 / 512000) (47251 / 512000) (150319489 / 125000000) (601353121 / 500000000) (3777829 / 1000000) (1889211 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (47219 / 512000) (47251 / 512000) (3777829 / 1000000) (1889211 / 500000) (34417 / 1000) (34439 / 1000)
    (5971 / 100) (60057 / 1000) (-70461 / 125) (331791 / 1000000) (3261083 / 1000) (1531579 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3777829 / 1000000) (16714781223 / 200000) (1531579 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3777829 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3777829 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell892 :
    ∀ t ∈ Set.Icc ((47251 / 512000) : ℝ) (47283 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1202706241 / 1000000000) : ℝ) ≤ Real.exp (2 * (47251 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47251 / 512000)) (1202706241 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((47283 / 512000) : ℝ)) ≤ (120285659 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47283 / 512000)) (120285659 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((83692330507 / 1000000) : ℝ) ≤ Real.exp (3 * (3778301 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3778301 / 1000000)) (83692330507 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((47251 / 512000) : ℝ) (47283 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3778301 / 1000000) (755779 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (47251 / 512000) (47283 / 512000) (1202706241 / 1000000000) (120285659 / 100000000) (3778301 / 1000000) (755779 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (47251 / 512000) (47283 / 512000) (3778301 / 1000000) (755779 / 200000) (8607 / 250) (34451 / 1000)
    (59771 / 1000) (1503 / 25) (-281873 / 500) (165723 / 500000) (3262717 / 1000) (3058823 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3778301 / 1000000) (83692330507 / 1000000) (3058823 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3778301 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3778301 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell893 :
    ∀ t ∈ Set.Icc ((47283 / 512000) : ℝ) (9463 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1202856589 / 1000000000) : ℝ) ≤ Real.exp (2 * (47283 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47283 / 512000)) (1202856589 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9463 / 102400) : ℝ)) ≤ (300751739 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9463 / 102400)) (300751739 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((83810922707 / 1000000) : ℝ) ≤ Real.exp (3 * (3778773 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3778773 / 1000000)) (83810922707 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((47283 / 512000) : ℝ) (9463 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3778773 / 1000000) (3779367 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (47283 / 512000) (9463 / 102400) (1202856589 / 1000000000) (300751739 / 250000000) (3778773 / 1000000) (3779367 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (47283 / 512000) (9463 / 102400) (3778773 / 1000000) (3779367 / 1000000) (861 / 25) (17231 / 500)
    (59833 / 1000) (60181 / 1000) (-563809 / 1000) (331101 / 1000000) (3264347 / 1000) (610899 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3778773 / 1000000) (83810922707 / 1000000) (610899 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3778773 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3778773 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell894 :
    ∀ t ∈ Set.Icc ((9463 / 102400) : ℝ) (47347 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((240601391 / 200000000) : ℝ) ≤ Real.exp (2 * (9463 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9463 / 102400)) (240601391 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((47347 / 512000) : ℝ)) ≤ (1203157341 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47347 / 512000)) (1203157341 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((83929934741 / 1000000) : ℝ) ≤ Real.exp (3 * (1889623 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1889623 / 500000)) (83929934741 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9463 / 102400) : ℝ) (47347 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1889623 / 500000) (11812 / 3125) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9463 / 102400) (47347 / 512000) (240601391 / 200000000) (1203157341 / 1000000000) (1889623 / 500000) (11812 / 3125) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9463 / 102400) (47347 / 512000) (1889623 / 500000) (11812 / 3125) (34451 / 1000) (17237 / 500)
    (11979 / 200) (60243 / 1000) (-70484 / 125) (82689 / 250000) (3265981 / 1000) (762541 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1889623 / 500000) (83929934741 / 1000000) (762541 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1889623 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1889623 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell895 :
    ∀ t ∈ Set.Icc ((47347 / 512000) : ℝ) (47379 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((60157867 / 50000000) : ℝ) ≤ Real.exp (2 * (47347 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47347 / 512000)) (60157867 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((47379 / 512000) : ℝ)) ≤ (240661549 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47379 / 512000)) (240661549 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((672390909 / 8000) : ℝ) ≤ Real.exp (3 * (1889859 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1889859 / 500000)) (672390909 / 8000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((47347 / 512000) : ℝ) (47379 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1889859 / 500000) (472539 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (47347 / 512000) (47379 / 512000) (60157867 / 50000000) (240661549 / 200000000) (1889859 / 500000) (472539 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (47347 / 512000) (47379 / 512000) (1889859 / 500000) (472539 / 125000) (34463 / 1000) (6897 / 200)
    (59957 / 1000) (12061 / 200) (-281967 / 500) (82603 / 250000) (3267613 / 1000) (380731 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1889859 / 500000) (672390909 / 8000) (380731 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1889859 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1889859 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell896 :
    ∀ t ∈ Set.Icc ((47379 / 512000) : ℝ) (47411 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((37603367 / 31250000) : ℝ) ≤ Real.exp (2 * (47379 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47379 / 512000)) (37603367 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((47411 / 512000) : ℝ)) ≤ (150432271 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47411 / 512000)) (150432271 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2630256673 / 31250) : ℝ) ≤ Real.exp (3 * (3780191 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3780191 / 1000000)) (2630256673 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((47379 / 512000) : ℝ) (47411 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3780191 / 1000000) (756157 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (47379 / 512000) (47411 / 512000) (37603367 / 31250000) (150432271 / 125000000) (3780191 / 1000000) (756157 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (47379 / 512000) (47411 / 512000) (3780191 / 1000000) (756157 / 200000) (17237 / 500) (34497 / 1000)
    (60019 / 1000) (60367 / 1000) (-563997 / 1000) (330067 / 1000000) (3269249 / 1000) (3041529 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3780191 / 1000000) (2630256673 / 31250) (3041529 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3780191 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3780191 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell897 :
    ∀ t ∈ Set.Icc ((47411 / 512000) : ℝ) (47443 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1203458167 / 1000000000) : ℝ) ≤ Real.exp (2 * (47411 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47411 / 512000)) (1203458167 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((47443 / 512000) : ℝ)) ≤ (120360861 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47443 / 512000)) (120360861 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((42143740031 / 500000) : ℝ) ≤ Real.exp (3 * (3780663 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3780663 / 1000000)) (42143740031 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((47411 / 512000) : ℝ) (47443 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3780663 / 1000000) (3781257 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (47411 / 512000) (47443 / 512000) (1203458167 / 1000000000) (120360861 / 100000000) (3780663 / 1000000) (3781257 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (47411 / 512000) (47443 / 512000) (3780663 / 1000000) (3781257 / 1000000) (17243 / 500) (8627 / 250)
    (60081 / 1000) (60429 / 1000) (-28203 / 50) (82431 / 250000) (1635441 / 500) (121489 / 40000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3780663 / 1000000) (42143740031 / 500000) (121489 / 40000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3780663 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3780663 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell898 :
    ∀ t ∈ Set.Icc ((47443 / 512000) : ℝ) (1899 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1203608609 / 1000000000) : ℝ) ≤ Real.exp (2 * (47443 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47443 / 512000)) (1203608609 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1899 / 20480) : ℝ)) ≤ (120375907 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1899 / 20480)) (120375907 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8440716881 / 100000) : ℝ) ≤ Real.exp (3 * (236321 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (236321 / 62500)) (8440716881 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((47443 / 512000) : ℝ) (1899 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (236321 / 62500) (378173 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (47443 / 512000) (1899 / 20480) (1203608609 / 1000000000) (120375907 / 100000000) (236321 / 62500) (378173 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (47443 / 512000) (1899 / 20480) (236321 / 62500) (378173 / 100000) (34497 / 1000) (863 / 25)
    (60143 / 1000) (15123 / 250) (-282061 / 500) (16469 / 50000) (3272519 / 1000) (1516459 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (236321 / 62500) (8440716881 / 100000) (1516459 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (236321 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (236321 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell899 :
    ∀ t ∈ Set.Icc ((1899 / 20480) : ℝ) (47507 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1203759069 / 1000000000) : ℝ) ≤ Real.exp (2 * (1899 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1899 / 20480)) (1203759069 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((47507 / 512000) : ℝ)) ≤ (24078191 / 20000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47507 / 512000)) (24078191 / 20000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((21131756879 / 250000) : ℝ) ≤ Real.exp (3 * (3781609 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3781609 / 1000000)) (21131756879 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1899 / 20480) : ℝ) (47507 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3781609 / 1000000) (3782203 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1899 / 20480) (47507 / 512000) (1203759069 / 1000000000) (24078191 / 20000000) (3781609 / 1000000) (3782203 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1899 / 20480) (47507 / 512000) (3781609 / 1000000) (3782203 / 1000000) (34509 / 1000) (34531 / 1000)
    (12041 / 200) (30277 / 500) (-70523 / 125) (82259 / 250000) (818539 / 250) (1514309 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3781609 / 1000000) (21131756879 / 250000) (1514309 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3781609 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3781609 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch044 :
    ∀ t ∈ Set.Icc ((46867 / 512000) : ℝ) (47507 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell880
      hpThetaDensityLowerExpCompact_cell881)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell882
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell883
      hpThetaDensityLowerExpCompact_cell884)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell885
      hpThetaDensityLowerExpCompact_cell886)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell887
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell888
      hpThetaDensityLowerExpCompact_cell889))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell890
      hpThetaDensityLowerExpCompact_cell891)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell892
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell893
      hpThetaDensityLowerExpCompact_cell894)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell895
      hpThetaDensityLowerExpCompact_cell896)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell897
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell898
      hpThetaDensityLowerExpCompact_cell899)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch044
end HodgeProofHP
