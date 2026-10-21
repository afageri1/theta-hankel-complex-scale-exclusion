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
theorem hpThetaDensityLowerExpCompact_cell480 :
    ∀ t ∈ Set.Icc ((42059 / 512000) : ℝ) (42063 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235711909 / 200000000) : ℝ) ≤ Real.exp (2 * (42059 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42059 / 512000)) (235711909 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42063 / 512000) : ℝ)) ≤ (1178577961 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42063 / 512000)) (1178577961 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13331618741 / 200000) : ℝ) ≤ Real.exp (3 * (925611 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (925611 / 250000)) (13331618741 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42059 / 512000) : ℝ) (42063 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (925611 / 250000) (3702621 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42059 / 512000) (42063 / 512000) (235711909 / 200000000) (1178577961 / 1000000000) (925611 / 250000) (3702621 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42059 / 512000) (42063 / 512000) (925611 / 250000) (3702621 / 1000000) (4077 / 125) (32623 / 1000)
    (25141 / 500) (50383 / 1000) (-138503 / 250) (391453 / 1000000) (751791 / 250) (1920247 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (925611 / 250000) (13331618741 / 200000) (1920247 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (925611 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (925611 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell481 :
    ∀ t ∈ Set.Icc ((42063 / 512000) : ℝ) (42067 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((29464449 / 25000000) : ℝ) ≤ Real.exp (2 * (42063 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42063 / 512000)) (29464449 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42067 / 512000) : ℝ)) ≤ (1178596377 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42067 / 512000)) (1178596377 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2083427913 / 31250) : ℝ) ≤ Real.exp (3 * (1851251 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1851251 / 500000)) (2083427913 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42063 / 512000) : ℝ) (42067 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1851251 / 500000) (3702679 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42063 / 512000) (42067 / 512000) (29464449 / 25000000) (1178596377 / 1000000000) (1851251 / 500000) (3702679 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42063 / 512000) (42067 / 512000) (1851251 / 500000) (3702679 / 1000000) (16309 / 500) (261 / 8)
    (50289 / 1000) (5039 / 100) (-277011 / 500) (391403 / 1000000) (375919 / 125) (1919913 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1851251 / 500000) (2083427913 / 31250) (1919913 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1851251 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1851251 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell482 :
    ∀ t ∈ Set.Icc ((42067 / 512000) : ℝ) (42071 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((147324547 / 125000000) : ℝ) ≤ Real.exp (2 * (42067 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42067 / 512000)) (147324547 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42071 / 512000) : ℝ)) ≤ (147326849 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42071 / 512000)) (147326849 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66681294747 / 1000000) : ℝ) ≤ Real.exp (3 * (23141 / 6250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (23141 / 6250)) (66681294747 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42067 / 512000) : ℝ) (42071 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (23141 / 6250) (3702737 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42067 / 512000) (42071 / 512000) (147324547 / 125000000) (147326849 / 125000000) (23141 / 6250) (3702737 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42067 / 512000) (42071 / 512000) (23141 / 6250) (3702737 / 1000000) (32619 / 1000) (16313 / 500)
    (6287 / 125) (50397 / 1000) (-69254 / 125) (391353 / 1000000) (3007541 / 1000) (1919579 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (23141 / 6250) (66681294747 / 1000000) (1919579 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (23141 / 6250)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (23141 / 6250)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell483 :
    ∀ t ∈ Set.Icc ((42071 / 512000) : ℝ) (1683 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1178614791 / 1000000000) : ℝ) ≤ Real.exp (2 * (42071 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42071 / 512000)) (1178614791 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1683 / 20480) : ℝ)) ≤ (147329151 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1683 / 20480)) (147329151 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8336612287 / 125000) : ℝ) ≤ Real.exp (3 * (1851309 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1851309 / 500000)) (8336612287 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42071 / 512000) : ℝ) (1683 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1851309 / 500000) (740559 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42071 / 512000) (1683 / 20480) (1178614791 / 1000000000) (147329151 / 125000000) (1851309 / 500000) (740559 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42071 / 512000) (1683 / 20480) (1851309 / 500000) (740559 / 200000) (1631 / 50) (8157 / 250)
    (50303 / 1000) (12601 / 250) (-277021 / 500) (391303 / 1000000) (3007729 / 1000) (383849 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1851309 / 500000) (8336612287 / 125000) (383849 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1851309 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1851309 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell484 :
    ∀ t ∈ Set.Icc ((1683 / 20480) : ℝ) (42079 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1178633207 / 1000000000) : ℝ) ≤ Real.exp (2 * (1683 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1683 / 20480)) (1178633207 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42079 / 512000) : ℝ)) ≤ (9429213 / 8000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42079 / 512000)) (9429213 / 8000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13340900773 / 200000) : ℝ) ≤ Real.exp (3 * (925669 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (925669 / 250000)) (13340900773 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1683 / 20480) : ℝ) (42079 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (925669 / 250000) (925713 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1683 / 20480) (42079 / 512000) (1178633207 / 1000000000) (9429213 / 8000000) (925669 / 250000) (925713 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1683 / 20480) (42079 / 512000) (925669 / 250000) (925713 / 250000) (16311 / 500) (32629 / 1000)
    (5031 / 100) (50411 / 1000) (-69257 / 125) (391253 / 1000000) (1503957 / 500) (1918911 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (925669 / 250000) (13340900773 / 200000) (1918911 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (925669 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (925669 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell485 :
    ∀ t ∈ Set.Icc ((42079 / 512000) : ℝ) (42083 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((147331453 / 125000000) : ℝ) ≤ Real.exp (2 * (42079 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42079 / 512000)) (147331453 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42083 / 512000) : ℝ)) ≤ (1178670041 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42083 / 512000)) (1178670041 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66716111453 / 1000000) : ℝ) ≤ Real.exp (3 * (1851367 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1851367 / 500000)) (66716111453 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42079 / 512000) : ℝ) (42083 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1851367 / 500000) (370291 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42079 / 512000) (42083 / 512000) (147331453 / 125000000) (1178670041 / 1000000000) (1851367 / 500000) (370291 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42079 / 512000) (42083 / 512000) (1851367 / 500000) (370291 / 100000) (32623 / 1000) (3263 / 100)
    (50317 / 1000) (25209 / 500) (-277033 / 500) (97801 / 250000) (3008103 / 1000) (767431 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1851367 / 500000) (66716111453 / 1000000) (767431 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1851367 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1851367 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell486 :
    ∀ t ∈ Set.Icc ((42083 / 512000) : ℝ) (42087 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((29466751 / 25000000) : ℝ) ≤ Real.exp (2 * (42083 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42083 / 512000)) (29466751 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42087 / 512000) : ℝ)) ≤ (589344229 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42087 / 512000)) (589344229 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((33363760439 / 500000) : ℝ) ≤ Real.exp (3 * (3702791 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3702791 / 1000000)) (33363760439 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42083 / 512000) : ℝ) (42087 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3702791 / 1000000) (462871 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42083 / 512000) (42087 / 512000) (29466751 / 25000000) (589344229 / 500000000) (3702791 / 1000000) (462871 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42083 / 512000) (42087 / 512000) (3702791 / 1000000) (462871 / 125000) (4078 / 125) (4079 / 125)
    (12581 / 250) (2017 / 40) (-69259 / 125) (78231 / 200000) (3008291 / 1000) (1918249 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3702791 / 1000000) (33363760439 / 500000) (1918249 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3702791 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3702791 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell487 :
    ∀ t ∈ Set.Icc ((42087 / 512000) : ℝ) (42091 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1178688457 / 1000000000) : ℝ) ≤ Real.exp (2 * (42087 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42087 / 512000)) (1178688457 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42091 / 512000) : ℝ)) ≤ (1885931 / 1600000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42091 / 512000)) (1885931 / 1600000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66739132471 / 1000000) : ℝ) ≤ Real.exp (3 * (3702849 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3702849 / 1000000)) (66739132471 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42087 / 512000) : ℝ) (42091 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3702849 / 1000000) (1851513 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42087 / 512000) (42091 / 512000) (1178688457 / 1000000000) (1885931 / 1600000) (3702849 / 1000000) (1851513 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42087 / 512000) (42091 / 512000) (3702849 / 1000000) (1851513 / 500000) (16313 / 500) (32633 / 1000)
    (50331 / 1000) (6304 / 125) (-277041 / 500) (195553 / 500000) (75212 / 25) (3835831 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3702849 / 1000000) (66739132471 / 1000000) (3835831 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3702849 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3702849 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell488 :
    ∀ t ∈ Set.Icc ((42091 / 512000) : ℝ) (8419 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((589353437 / 500000000) : ℝ) ≤ Real.exp (2 * (42091 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42091 / 512000)) (589353437 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8419 / 102400) : ℝ)) ≤ (1178725293 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8419 / 102400)) (1178725293 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13350149217 / 200000) : ℝ) ≤ Real.exp (3 * (3702907 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3702907 / 1000000)) (13350149217 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42091 / 512000) : ℝ) (8419 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3702907 / 1000000) (925771 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42091 / 512000) (8419 / 102400) (589353437 / 500000000) (1178725293 / 1000000000) (3702907 / 1000000) (925771 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42091 / 512000) (8419 / 102400) (3702907 / 1000000) (925771 / 250000) (32627 / 1000) (16317 / 500)
    (25169 / 500) (50439 / 1000) (-138523 / 250) (24441 / 62500) (752167 / 250) (958791 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3702907 / 1000000) (13350149217 / 200000) (958791 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3702907 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3702907 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell489 :
    ∀ t ∈ Set.Icc ((8419 / 102400) : ℝ) (42099 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((294681323 / 250000000) : ℝ) ≤ Real.exp (2 * (8419 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8419 / 102400)) (294681323 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42099 / 512000) : ℝ)) ≤ (117874371 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42099 / 512000)) (117874371 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1669059043 / 25000) : ℝ) ≤ Real.exp (3 * (740593 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (740593 / 200000)) (1669059043 / 25000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8419 / 102400) : ℝ) (42099 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (740593 / 200000) (1851571 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8419 / 102400) (42099 / 512000) (294681323 / 250000000) (117874371 / 100000000) (740593 / 200000) (1851571 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8419 / 102400) (42099 / 512000) (740593 / 200000) (1851571 / 500000) (8157 / 250) (8159 / 250)
    (10069 / 200) (25223 / 500) (-277051 / 500) (195503 / 500000) (3008857 / 1000) (29957 / 7812500)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (740593 / 200000) (1669059043 / 25000) (29957 / 7812500)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (740593 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (740593 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell490 :
    ∀ t ∈ Set.Icc ((42099 / 512000) : ℝ) (42103 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1178743709 / 1000000000) : ℝ) ≤ Real.exp (2 * (42099 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42099 / 512000)) (1178743709 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42103 / 512000) : ℝ)) ≤ (73672633 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42103 / 512000)) (73672633 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4173373711 / 62500) : ℝ) ≤ Real.exp (3 * (3703023 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3703023 / 1000000)) (4173373711 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42099 / 512000) : ℝ) (42103 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3703023 / 1000000) (4629 / 1250) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42099 / 512000) (42103 / 512000) (1178743709 / 1000000000) (73672633 / 62500000) (3703023 / 1000000) (4629 / 1250) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42099 / 512000) (42103 / 512000) (3703023 / 1000000) (4629 / 1250) (3263 / 100) (32637 / 1000)
    (6294 / 125) (50453 / 1000) (-69264 / 125) (390957 / 1000000) (601809 / 200) (3833829 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3703023 / 1000000) (4173373711 / 62500) (3833829 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3703023 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3703023 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell491 :
    ∀ t ∈ Set.Icc ((42103 / 512000) : ℝ) (42107 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1178762127 / 1000000000) : ℝ) ≤ Real.exp (2 * (42103 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42103 / 512000)) (1178762127 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42107 / 512000) : ℝ)) ≤ (1178780547 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42107 / 512000)) (1178780547 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((33392799527 / 500000) : ℝ) ≤ Real.exp (3 * (3703081 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3703081 / 1000000)) (33392799527 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42103 / 512000) : ℝ) (42107 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3703081 / 1000000) (3703257 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42103 / 512000) (42107 / 512000) (1178762127 / 1000000000) (1178780547 / 1000000000) (3703081 / 1000000) (3703257 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42103 / 512000) (42107 / 512000) (3703081 / 1000000) (3703257 / 1000000) (32631 / 1000) (16319 / 500)
    (50359 / 1000) (2523 / 50) (-277063 / 500) (390907 / 1000000) (3009231 / 1000) (1916581 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3703081 / 1000000) (33392799527 / 500000) (1916581 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3703081 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3703081 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell492 :
    ∀ t ∈ Set.Icc ((42107 / 512000) : ℝ) (42111 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((589390273 / 500000000) : ℝ) ≤ Real.exp (2 * (42107 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42107 / 512000)) (589390273 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42111 / 512000) : ℝ)) ≤ (235759793 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42111 / 512000)) (235759793 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66797220753 / 1000000) : ℝ) ≤ Real.exp (3 * (3703139 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3703139 / 1000000)) (66797220753 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42107 / 512000) : ℝ) (42111 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3703139 / 1000000) (740663 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42107 / 512000) (42111 / 512000) (589390273 / 500000000) (235759793 / 200000000) (3703139 / 1000000) (740663 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42107 / 512000) (42111 / 512000) (3703139 / 1000000) (740663 / 200000) (32633 / 1000) (816 / 25)
    (50367 / 1000) (50467 / 1000) (-69267 / 125) (390857 / 1000000) (3009419 / 1000) (766499 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3703139 / 1000000) (66797220753 / 1000000) (766499 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3703139 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3703139 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell493 :
    ∀ t ∈ Set.Icc ((42111 / 512000) : ℝ) (8423 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((294699741 / 250000000) : ℝ) ≤ Real.exp (2 * (42111 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42111 / 512000)) (294699741 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8423 / 102400) : ℝ)) ≤ (147352173 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8423 / 102400)) (147352173 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66808644049 / 1000000) : ℝ) ≤ Real.exp (3 * (925799 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (925799 / 250000)) (66808644049 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42111 / 512000) : ℝ) (8423 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (925799 / 250000) (3703373 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42111 / 512000) (8423 / 102400) (294699741 / 250000000) (147352173 / 125000000) (925799 / 250000) (3703373 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42111 / 512000) (8423 / 102400) (925799 / 250000) (3703373 / 1000000) (16317 / 500) (32641 / 1000)
    (50373 / 1000) (2019 / 40) (-277071 / 500) (48851 / 125000) (376201 / 125) (23949 / 6250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (925799 / 250000) (66808644049 / 1000000) (23949 / 6250000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (925799 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (925799 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell494 :
    ∀ t ∈ Set.Icc ((8423 / 102400) : ℝ) (42119 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1178817383 / 1000000000) : ℝ) ≤ Real.exp (2 * (8423 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8423 / 102400)) (1178817383 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42119 / 512000) : ℝ)) ≤ (1178835803 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42119 / 512000)) (1178835803 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66820269759 / 1000000) : ℝ) ≤ Real.exp (3 * (1851627 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1851627 / 500000)) (66820269759 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8423 / 102400) : ℝ) (42119 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1851627 / 500000) (3703431 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8423 / 102400) (42119 / 512000) (1178817383 / 1000000000) (1178835803 / 1000000000) (1851627 / 500000) (3703431 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8423 / 102400) (42119 / 512000) (1851627 / 500000) (3703431 / 1000000) (6527 / 200) (32643 / 1000)
    (2519 / 50) (25241 / 500) (-69269 / 125) (390759 / 1000000) (752449 / 250) (3831173 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1851627 / 500000) (66820269759 / 1000000) (3831173 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1851627 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1851627 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell495 :
    ∀ t ∈ Set.Icc ((42119 / 512000) : ℝ) (42123 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((589417901 / 500000000) : ℝ) ≤ Real.exp (2 * (42119 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42119 / 512000)) (589417901 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42123 / 512000) : ℝ)) ≤ (1178854223 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42123 / 512000)) (1178854223 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16707974373 / 250000) : ℝ) ≤ Real.exp (3 * (231457 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (231457 / 62500)) (16707974373 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42119 / 512000) : ℝ) (42123 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (231457 / 62500) (3703489 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42119 / 512000) (42123 / 512000) (589417901 / 500000000) (1178854223 / 1000000000) (231457 / 62500) (3703489 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42119 / 512000) (42123 / 512000) (231457 / 62500) (3703489 / 1000000) (32637 / 1000) (8161 / 250)
    (50387 / 1000) (50489 / 1000) (-277081 / 500) (390709 / 1000000) (601997 / 200) (3830507 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (231457 / 62500) (16707974373 / 250000) (3830507 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (231457 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (231457 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell496 :
    ∀ t ∈ Set.Icc ((42123 / 512000) : ℝ) (42127 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((589427111 / 500000000) : ℝ) ≤ Real.exp (2 * (42123 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42123 / 512000)) (589427111 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42127 / 512000) : ℝ)) ≤ (1178872643 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42127 / 512000)) (1178872643 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66843527249 / 1000000) : ℝ) ≤ Real.exp (3 * (370337 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (370337 / 100000)) (66843527249 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42123 / 512000) : ℝ) (42127 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (370337 / 100000) (3703547 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42123 / 512000) (42127 / 512000) (589427111 / 500000000) (1178872643 / 1000000000) (370337 / 100000) (3703547 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42123 / 512000) (42127 / 512000) (370337 / 100000) (3703547 / 1000000) (16319 / 500) (6529 / 200)
    (25197 / 500) (6312 / 125) (-138543 / 250) (19533 / 50000) (3010173 / 1000) (47873 / 12500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (370337 / 100000) (66843527249 / 1000000) (47873 / 12500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (370337 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (370337 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell497 :
    ∀ t ∈ Set.Icc ((42127 / 512000) : ℝ) (42131 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((589436321 / 500000000) : ℝ) ≤ Real.exp (2 * (42127 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42127 / 512000)) (589436321 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42131 / 512000) : ℝ)) ≤ (1178891063 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42131 / 512000)) (1178891063 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66855159029 / 1000000) : ℝ) ≤ Real.exp (3 * (925857 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (925857 / 250000)) (66855159029 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42127 / 512000) : ℝ) (42131 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (925857 / 250000) (740721 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42127 / 512000) (42131 / 512000) (589436321 / 500000000) (1178891063 / 1000000000) (925857 / 250000) (740721 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42127 / 512000) (42131 / 512000) (925857 / 250000) (740721 / 200000) (32639 / 1000) (32647 / 1000)
    (25201 / 500) (50503 / 1000) (-277091 / 500) (39061 / 100000) (1505181 / 500) (1914587 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (925857 / 250000) (66855159029 / 1000000) (1914587 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (925857 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (925857 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell498 :
    ∀ t ∈ Set.Icc ((42131 / 512000) : ℝ) (8427 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((589445531 / 500000000) : ℝ) ≤ Real.exp (2 * (42131 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42131 / 512000)) (589445531 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8427 / 102400) : ℝ)) ≤ (1178909483 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8427 / 102400)) (1178909483 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66866792833 / 1000000) : ℝ) ≤ Real.exp (3 * (1851743 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1851743 / 500000)) (66866792833 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42131 / 512000) : ℝ) (8427 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1851743 / 500000) (3703663 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42131 / 512000) (8427 / 102400) (589445531 / 500000000) (1178909483 / 1000000000) (1851743 / 500000) (3703663 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42131 / 512000) (8427 / 102400) (1851743 / 500000) (3703663 / 1000000) (32641 / 1000) (4081 / 125)
    (50409 / 1000) (5051 / 100) (-69274 / 125) (2441 / 6250) (60211 / 20) (957127 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1851743 / 500000) (66866792833 / 1000000) (957127 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1851743 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1851743 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell499 :
    ∀ t ∈ Set.Icc ((8427 / 102400) : ℝ) (42139 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((589454741 / 500000000) : ℝ) ≤ Real.exp (2 * (8427 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8427 / 102400)) (589454741 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42139 / 512000) : ℝ)) ≤ (36841497 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42139 / 512000)) (36841497 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((33439214331 / 500000) : ℝ) ≤ Real.exp (3 * (462943 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (462943 / 125000)) (33439214331 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8427 / 102400) : ℝ) (42139 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (462943 / 125000) (92593 / 25000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8427 / 102400) (42139 / 512000) (589454741 / 500000000) (36841497 / 31250000) (462943 / 125000) (92593 / 25000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8427 / 102400) (42139 / 512000) (462943 / 125000) (92593 / 25000) (16321 / 500) (32649 / 1000)
    (6302 / 125) (50517 / 1000) (-277103 / 500) (39051 / 100000) (376342 / 125) (1913921 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (462943 / 125000) (33439214331 / 500000) (1913921 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (462943 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (462943 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch024 :
    ∀ t ∈ Set.Icc ((42059 / 512000) : ℝ) (42139 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell480
      hpThetaDensityLowerExpCompact_cell481)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell482
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell483
      hpThetaDensityLowerExpCompact_cell484)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell485
      hpThetaDensityLowerExpCompact_cell486)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell487
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell488
      hpThetaDensityLowerExpCompact_cell489))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell490
      hpThetaDensityLowerExpCompact_cell491)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell492
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell493
      hpThetaDensityLowerExpCompact_cell494)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell495
      hpThetaDensityLowerExpCompact_cell496)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell497
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell498
      hpThetaDensityLowerExpCompact_cell499)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch024
end HodgeProofHP
