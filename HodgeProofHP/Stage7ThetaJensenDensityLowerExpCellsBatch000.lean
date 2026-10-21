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
theorem hpThetaDensityLowerExpCompact_cell000 :
    ∀ t ∈ Set.Icc ((2 / 25) : ℝ) (40961 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((117351087 / 100000000) : ℝ) ≤ Real.exp (2 * (2 / 25)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2 / 25)) (117351087 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((40961 / 512000) : ℝ)) ≤ (18336179 / 15625000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (40961 / 512000)) (18336179 / 15625000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31780386291 / 500000) : ℝ) ≤ Real.exp (3 * (460823 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (460823 / 125000)) (31780386291 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2 / 25) : ℝ) (40961 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (460823 / 125000) (3686717 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2 / 25) (40961 / 512000) (117351087 / 100000000) (18336179 / 15625000) (460823 / 125000) (3686717 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2 / 25) (40961 / 512000) (460823 / 125000) (3686717 / 1000000) (32243 / 1000) (32249 / 1000)
    (24187 / 500) (969 / 20) (-275703 / 500) (405261 / 1000000) (2955829 / 1000) (2013821 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (460823 / 125000) (31780386291 / 500000) (2013821 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (460823 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (460823 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell001 :
    ∀ t ∈ Set.Icc ((40961 / 512000) : ℝ) (20481 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((234703091 / 200000000) : ℝ) ≤ Real.exp (2 * (40961 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (40961 / 512000)) (234703091 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20481 / 256000) : ℝ)) ≤ (29338001 / 25000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20481 / 256000)) (29338001 / 25000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6356344219 / 100000) : ℝ) ≤ Real.exp (3 * (1843299 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1843299 / 500000)) (6356344219 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((40961 / 512000) : ℝ) (20481 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1843299 / 500000) (3686731 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (40961 / 512000) (20481 / 256000) (234703091 / 200000000) (29338001 / 25000000) (1843299 / 500000) (3686731 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (40961 / 512000) (20481 / 256000) (1843299 / 500000) (3686731 / 1000000) (32243 / 1000) (32249 / 1000)
    (387 / 8) (48451 / 1000) (-68926 / 125) (6332 / 15625) (1477937 / 500) (4027473 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1843299 / 500000) (6356344219 / 100000) (4027473 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843299 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843299 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell002 :
    ∀ t ∈ Set.Icc ((20481 / 256000) : ℝ) (40963 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173520039 / 1000000000) : ℝ) ≤ Real.exp (2 * (20481 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20481 / 256000)) (1173520039 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((40963 / 512000) : ℝ)) ≤ (73345289 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (40963 / 512000)) (73345289 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3972893913 / 62500) : ℝ) ≤ Real.exp (3 * (3686613 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3686613 / 1000000)) (3972893913 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20481 / 256000) : ℝ) (40963 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3686613 / 1000000) (737349 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20481 / 256000) (40963 / 512000) (1173520039 / 1000000000) (73345289 / 62500000) (3686613 / 1000000) (737349 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20481 / 256000) (40963 / 512000) (3686613 / 1000000) (737349 / 200000) (32243 / 1000) (32249 / 1000)
    (48377 / 1000) (48453 / 1000) (-110283 / 200) (81047 / 200000) (2955919 / 1000) (1006823 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3686613 / 1000000) (3972893913 / 62500) (1006823 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3686613 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3686613 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell003 :
    ∀ t ∈ Set.Icc ((40963 / 512000) : ℝ) (10241 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173524623 / 1000000000) : ℝ) ≤ Real.exp (2 * (40963 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (40963 / 512000)) (1173524623 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((10241 / 128000) : ℝ)) ≤ (146691151 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (10241 / 128000)) (146691151 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63568972447 / 1000000) : ℝ) ≤ Real.exp (3 * (3686627 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3686627 / 1000000)) (63568972447 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((40963 / 512000) : ℝ) (10241 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3686627 / 1000000) (92169 / 25000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (40963 / 512000) (10241 / 128000) (1173524623 / 1000000000) (146691151 / 125000000) (3686627 / 1000000) (92169 / 25000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (40963 / 512000) (10241 / 128000) (3686627 / 1000000) (92169 / 25000) (8061 / 250) (129 / 4)
    (48379 / 1000) (9691 / 200) (-551413 / 1000) (405223 / 1000000) (2955967 / 1000) (2013561 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3686627 / 1000000) (63568972447 / 1000000) (2013561 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3686627 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3686627 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell004 :
    ∀ t ∈ Set.Icc ((10241 / 128000) : ℝ) (8193 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173529207 / 1000000000) : ℝ) ≤ Real.exp (2 * (10241 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (10241 / 128000)) (1173529207 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8193 / 102400) : ℝ)) ≤ (36672931 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8193 / 102400)) (36672931 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31785916557 / 500000) : ℝ) ≤ Real.exp (3 * (1843321 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1843321 / 500000)) (31785916557 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((10241 / 128000) : ℝ) (8193 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1843321 / 500000) (1843387 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (10241 / 128000) (8193 / 102400) (1173529207 / 1000000000) (36672931 / 31250000) (1843321 / 500000) (1843387 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (10241 / 128000) (8193 / 102400) (1843321 / 500000) (1843387 / 500000) (8061 / 250) (129 / 4)
    (48381 / 1000) (6057 / 125) (-551421 / 1000) (405209 / 1000000) (739003 / 250) (4026941 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1843321 / 500000) (31785916557 / 500000) (4026941 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843321 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843321 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell005 :
    ∀ t ∈ Set.Icc ((8193 / 102400) : ℝ) (20483 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173533791 / 1000000000) : ℝ) ≤ Real.exp (2 * (8193 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8193 / 102400)) (1173533791 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20483 / 256000) : ℝ)) ≤ (146692297 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20483 / 256000)) (146692297 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31787251593 / 500000) : ℝ) ≤ Real.exp (3 * (57604 / 15625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (57604 / 15625)) (31787251593 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8193 / 102400) : ℝ) (20483 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (57604 / 15625) (3686789 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8193 / 102400) (20483 / 256000) (1173533791 / 1000000000) (146692297 / 125000000) (57604 / 15625) (3686789 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8193 / 102400) (20483 / 256000) (57604 / 15625) (3686789 / 1000000) (8061 / 250) (129 / 4)
    (24191 / 500) (24229 / 500) (-551419 / 1000) (405197 / 1000000) (147803 / 50) (1006693 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (57604 / 15625) (31787251593 / 500000) (1006693 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (57604 / 15625)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (57604 / 15625)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell006 :
    ∀ t ∈ Set.Icc ((20483 / 256000) : ℝ) (40967 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((9388307 / 8000000) : ℝ) ≤ Real.exp (2 * (20483 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20483 / 256000)) (9388307 / 8000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((40967 / 512000) : ℝ)) ≤ (14669287 / 12500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (40967 / 512000)) (14669287 / 12500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6357717337 / 100000) : ℝ) ≤ Real.exp (3 * (368667 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (368667 / 100000)) (6357717337 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20483 / 256000) : ℝ) (40967 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (368667 / 100000) (3686803 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20483 / 256000) (40967 / 512000) (9388307 / 8000000) (14669287 / 12500000) (368667 / 100000) (3686803 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20483 / 256000) (40967 / 512000) (368667 / 100000) (3686803 / 1000000) (6449 / 200) (32251 / 1000)
    (6048 / 125) (2423 / 50) (-551421 / 1000) (81037 / 200000) (591221 / 200) (4026603 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (368667 / 100000) (6357717337 / 100000) (4026603 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (368667 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (368667 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell007 :
    ∀ t ∈ Set.Icc ((40967 / 512000) : ℝ) (5121 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173542959 / 1000000000) : ℝ) ≤ Real.exp (2 * (40967 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (40967 / 512000)) (1173542959 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((5121 / 64000) : ℝ)) ≤ (146693443 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (5121 / 64000)) (146693443 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31790017203 / 500000) : ℝ) ≤ Real.exp (3 * (737337 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (737337 / 200000)) (31790017203 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((40967 / 512000) : ℝ) (5121 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (737337 / 200000) (3686817 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (40967 / 512000) (5121 / 64000) (1173542959 / 1000000000) (146693443 / 125000000) (737337 / 200000) (3686817 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (40967 / 512000) (5121 / 64000) (737337 / 200000) (3686817 / 1000000) (6449 / 200) (32251 / 1000)
    (24193 / 500) (48461 / 1000) (-137857 / 250) (405171 / 1000000) (2956149 / 1000) (2013211 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (737337 / 200000) (31790017203 / 500000) (2013211 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (737337 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (737337 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell008 :
    ∀ t ∈ Set.Icc ((5121 / 64000) : ℝ) (40969 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173547543 / 1000000000) : ℝ) ≤ Real.exp (2 * (5121 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (5121 / 64000)) (1173547543 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((40969 / 512000) : ℝ)) ≤ (2292094 / 1953125) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (40969 / 512000)) (2292094 / 1953125) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31791352411 / 500000) : ℝ) ≤ Real.exp (3 * (3686699 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3686699 / 1000000)) (31791352411 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((5121 / 64000) : ℝ) (40969 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3686699 / 1000000) (230427 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (5121 / 64000) (40969 / 512000) (1173547543 / 1000000000) (2292094 / 1953125) (3686699 / 1000000) (230427 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (5121 / 64000) (40969 / 512000) (3686699 / 1000000) (230427 / 62500) (16123 / 500) (32251 / 1000)
    (12097 / 250) (48463 / 1000) (-275713 / 500) (405159 / 1000000) (1478099 / 500) (4026253 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3686699 / 1000000) (31791352411 / 500000) (4026253 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3686699 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3686699 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell009 :
    ∀ t ∈ Set.Icc ((40969 / 512000) : ℝ) (4097 / 51200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173552127 / 1000000000) : ℝ) ≤ Real.exp (2 * (40969 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (40969 / 512000)) (1173552127 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4097 / 51200) : ℝ)) ≤ (1173556713 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4097 / 51200)) (1173556713 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63585566107 / 1000000) : ℝ) ≤ Real.exp (3 * (1843357 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1843357 / 500000)) (63585566107 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((40969 / 512000) : ℝ) (4097 / 51200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1843357 / 500000) (1843423 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (40969 / 512000) (4097 / 51200) (1173552127 / 1000000000) (1173556713 / 1000000000) (1843357 / 500000) (1843423 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (40969 / 512000) (4097 / 51200) (1843357 / 500000) (1843423 / 500000) (16123 / 500) (8063 / 250)
    (4839 / 100) (9693 / 200) (-275717 / 500) (81029 / 200000) (1478121 / 500) (4026071 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1843357 / 500000) (63585566107 / 1000000) (4026071 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843357 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843357 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell010 :
    ∀ t ∈ Set.Icc ((4097 / 51200) : ℝ) (40971 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((146694589 / 125000000) : ℝ) ≤ Real.exp (2 * (4097 / 51200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4097 / 51200)) (146694589 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((40971 / 512000) : ℝ)) ≤ (1173561297 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (40971 / 512000)) (1173561297 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15897059189 / 250000) : ℝ) ≤ Real.exp (3 * (460841 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (460841 / 125000)) (15897059189 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4097 / 51200) : ℝ) (40971 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (460841 / 125000) (3686861 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (4097 / 51200) (40971 / 512000) (146694589 / 125000000) (1173561297 / 1000000000) (460841 / 125000) (3686861 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (4097 / 51200) (40971 / 512000) (460841 / 125000) (3686861 / 1000000) (16123 / 500) (8063 / 250)
    (48391 / 1000) (48467 / 1000) (-68929 / 125) (405133 / 1000000) (2956291 / 1000) (2012951 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (460841 / 125000) (15897059189 / 250000) (2012951 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (460841 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (460841 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell011 :
    ∀ t ∈ Set.Icc ((40971 / 512000) : ℝ) (10243 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((73347581 / 62500000) : ℝ) ≤ Real.exp (2 * (40971 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (40971 / 512000)) (73347581 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((10243 / 128000) : ℝ)) ≤ (1173565881 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (10243 / 128000)) (1173565881 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63590907517 / 1000000) : ℝ) ≤ Real.exp (3 * (1843371 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1843371 / 500000)) (63590907517 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((40971 / 512000) : ℝ) (10243 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1843371 / 500000) (5899 / 1600) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (40971 / 512000) (10243 / 128000) (73347581 / 62500000) (1173565881 / 1000000000) (1843371 / 500000) (5899 / 1600) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (40971 / 512000) (10243 / 128000) (1843371 / 500000) (5899 / 1600) (32247 / 1000) (8063 / 250)
    (48393 / 1000) (48469 / 1000) (-275717 / 500) (405121 / 1000000) (591267 / 200) (4025733 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1843371 / 500000) (63590907517 / 1000000) (4025733 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843371 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843371 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell012 :
    ∀ t ∈ Set.Icc ((10243 / 128000) : ℝ) (40973 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((29339147 / 25000000) : ℝ) ≤ Real.exp (2 * (10243 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (10243 / 128000)) (29339147 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((40973 / 512000) : ℝ)) ≤ (234714093 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (40973 / 512000)) (234714093 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63593769171 / 1000000) : ℝ) ≤ Real.exp (3 * (3686757 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3686757 / 1000000)) (63593769171 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((10243 / 128000) : ℝ) (40973 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3686757 / 1000000) (3686889 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (10243 / 128000) (40973 / 512000) (29339147 / 25000000) (234714093 / 200000000) (3686757 / 1000000) (3686889 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (10243 / 128000) (40973 / 512000) (3686757 / 1000000) (3686889 / 1000000) (32247 / 1000) (32253 / 1000)
    (9679 / 200) (4847 / 100) (-551441 / 1000) (405107 / 1000000) (147819 / 50) (251597 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3686757 / 1000000) (63593769171 / 1000000) (251597 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3686757 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3686757 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell013 :
    ∀ t ∈ Set.Icc ((40973 / 512000) : ℝ) (20487 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((36674077 / 31250000) : ℝ) ≤ Real.exp (2 * (40973 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (40973 / 512000)) (36674077 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20487 / 256000) : ℝ)) ≤ (23471501 / 20000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20487 / 256000)) (23471501 / 20000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15899110041 / 250000) : ℝ) ≤ Real.exp (3 * (3686771 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3686771 / 1000000)) (15899110041 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((40973 / 512000) : ℝ) (20487 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3686771 / 1000000) (460863 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (40973 / 512000) (20487 / 256000) (36674077 / 31250000) (23471501 / 20000000) (3686771 / 1000000) (460863 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (40973 / 512000) (20487 / 256000) (3686771 / 1000000) (460863 / 125000) (32247 / 1000) (32253 / 1000)
    (12099 / 250) (6059 / 125) (-551439 / 1000) (81019 / 200000) (739107 / 250) (4025383 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3686771 / 1000000) (15899110041 / 250000) (4025383 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3686771 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3686771 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell014 :
    ∀ t ∈ Set.Icc ((20487 / 256000) : ℝ) (1639 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173575049 / 1000000000) : ℝ) ≤ Real.exp (2 * (20487 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20487 / 256000)) (1173575049 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1639 / 20480) : ℝ)) ≤ (586789817 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1639 / 20480)) (586789817 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63599302067 / 1000000) : ℝ) ≤ Real.exp (3 * (1843393 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1843393 / 500000)) (63599302067 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20487 / 256000) : ℝ) (1639 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1843393 / 500000) (1843459 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20487 / 256000) (1639 / 20480) (1173575049 / 1000000000) (586789817 / 500000000) (1843393 / 500000) (1843459 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20487 / 256000) (1639 / 20480) (1843393 / 500000) (1843459 / 500000) (4031 / 125) (32253 / 1000)
    (24199 / 500) (48473 / 1000) (-551447 / 1000) (405081 / 1000000) (2956473 / 1000) (2012601 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1843393 / 500000) (63599302067 / 1000000) (2012601 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843393 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843393 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell015 :
    ∀ t ∈ Set.Icc ((1639 / 20480) : ℝ) (2561 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173579633 / 1000000000) : ℝ) ≤ Real.exp (2 * (1639 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1639 / 20480)) (1173579633 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2561 / 32000) : ℝ)) ≤ (586792109 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2561 / 32000)) (586792109 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15900493323 / 250000) : ℝ) ≤ Real.exp (3 * (9217 / 2500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (9217 / 2500)) (15900493323 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1639 / 20480) : ℝ) (2561 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (9217 / 2500) (3686933 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1639 / 20480) (2561 / 32000) (1173579633 / 1000000000) (586792109 / 500000000) (9217 / 2500) (3686933 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1639 / 20480) (2561 / 32000) (9217 / 2500) (3686933 / 1000000) (4031 / 125) (16127 / 500)
    (242 / 5) (12119 / 250) (-110289 / 200) (405069 / 1000000) (2956521 / 1000) (4025033 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (9217 / 2500) (15900493323 / 250000) (4025033 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (9217 / 2500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (9217 / 2500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell016 :
    ∀ t ∈ Set.Icc ((2561 / 32000) : ℝ) (40977 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173584217 / 1000000000) : ℝ) ≤ Real.exp (2 * (2561 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2561 / 32000)) (1173584217 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((40977 / 512000) : ℝ)) ≤ (1173588803 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (40977 / 512000)) (1173588803 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6360464463 / 100000) : ℝ) ≤ Real.exp (3 * (1843407 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1843407 / 500000)) (6360464463 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2561 / 32000) : ℝ) (40977 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1843407 / 500000) (3686947 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2561 / 32000) (40977 / 512000) (1173584217 / 1000000000) (1173588803 / 1000000000) (1843407 / 500000) (3686947 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2561 / 32000) (40977 / 512000) (1843407 / 500000) (3686947 / 1000000) (4031 / 125) (16127 / 500)
    (48401 / 1000) (48477 / 1000) (-551447 / 1000) (405057 / 1000000) (1478283 / 500) (125777 / 31250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1843407 / 500000) (6360464463 / 100000) (125777 / 31250000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843407 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843407 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell017 :
    ∀ t ∈ Set.Icc ((40977 / 512000) : ℝ) (20489 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((586794401 / 500000000) : ℝ) ≤ Real.exp (2 * (40977 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (40977 / 512000)) (586794401 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20489 / 256000) : ℝ)) ≤ (1173593387 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20489 / 256000)) (1173593387 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31803753451 / 500000) : ℝ) ≤ Real.exp (3 * (3686829 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3686829 / 1000000)) (31803753451 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((40977 / 512000) : ℝ) (20489 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3686829 / 1000000) (3686961 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (40977 / 512000) (20489 / 256000) (586794401 / 500000000) (1173593387 / 1000000000) (3686829 / 1000000) (3686961 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (40977 / 512000) (20489 / 256000) (3686829 / 1000000) (3686961 / 1000000) (32249 / 1000) (16127 / 500)
    (48403 / 1000) (48479 / 1000) (-275727 / 500) (405043 / 1000000) (2956611 / 1000) (4024683 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3686829 / 1000000) (31803753451 / 500000) (4024683 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3686829 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3686829 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell018 :
    ∀ t ∈ Set.Icc ((20489 / 256000) : ℝ) (40979 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((586796693 / 500000000) : ℝ) ≤ Real.exp (2 * (20489 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20489 / 256000)) (586796693 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((40979 / 512000) : ℝ)) ≤ (1173597971 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (40979 / 512000)) (1173597971 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63610178473 / 1000000) : ℝ) ≤ Real.exp (3 * (3686843 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3686843 / 1000000)) (63610178473 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20489 / 256000) : ℝ) (40979 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3686843 / 1000000) (57609 / 15625) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20489 / 256000) (40979 / 512000) (586796693 / 500000000) (1173597971 / 1000000000) (3686843 / 1000000) (57609 / 15625) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20489 / 256000) (40979 / 512000) (3686843 / 1000000) (57609 / 15625) (32249 / 1000) (6451 / 200)
    (9681 / 200) (48481 / 1000) (-137863 / 250) (405031 / 1000000) (2956659 / 1000) (2012257 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3686843 / 1000000) (63610178473 / 1000000) (2012257 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3686843 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3686843 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell019 :
    ∀ t ∈ Set.Icc ((40979 / 512000) : ℝ) (2049 / 25600), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((117359797 / 100000000) : ℝ) ≤ Real.exp (2 * (40979 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (40979 / 512000)) (117359797 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2049 / 25600) : ℝ)) ≤ (293400639 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2049 / 25600)) (293400639 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31806520497 / 500000) : ℝ) ≤ Real.exp (3 * (1843429 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1843429 / 500000)) (31806520497 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((40979 / 512000) : ℝ) (2049 / 25600),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1843429 / 500000) (368699 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (40979 / 512000) (2049 / 25600) (117359797 / 100000000) (293400639 / 250000000) (1843429 / 500000) (368699 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (40979 / 512000) (2049 / 25600) (1843429 / 500000) (368699 / 100000) (32249 / 1000) (6451 / 200)
    (48407 / 1000) (24241 / 500) (-27573 / 50) (202509 / 500000) (369588 / 125) (4024333 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1843429 / 500000) (31806520497 / 500000) (4024333 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843429 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843429 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch000 :
    ∀ t ∈ Set.Icc ((2 / 25) : ℝ) (2049 / 25600),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell000
      hpThetaDensityLowerExpCompact_cell001)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell002
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell003
      hpThetaDensityLowerExpCompact_cell004)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell005
      hpThetaDensityLowerExpCompact_cell006)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell007
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell008
      hpThetaDensityLowerExpCompact_cell009))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell010
      hpThetaDensityLowerExpCompact_cell011)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell012
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell013
      hpThetaDensityLowerExpCompact_cell014)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell015
      hpThetaDensityLowerExpCompact_cell016)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell017
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell018
      hpThetaDensityLowerExpCompact_cell019)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch000
end HodgeProofHP
