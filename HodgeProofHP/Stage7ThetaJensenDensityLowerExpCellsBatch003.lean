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
theorem hpThetaDensityLowerExpCompact_cell060 :
    ∀ t ∈ Set.Icc ((2051 / 25600) : ℝ) (41021 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((146723243 / 125000000) : ℝ) ≤ Real.exp (2 * (2051 / 25600)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2051 / 25600)) (146723243 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41021 / 512000) : ℝ)) ≤ (117379053 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41021 / 512000)) (117379053 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63725735733 / 1000000) : ℝ) ≤ Real.exp (3 * (460931 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (460931 / 125000)) (63725735733 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2051 / 25600) : ℝ) (41021 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (460931 / 125000) (3687581 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2051 / 25600) (41021 / 512000) (146723243 / 125000000) (117379053 / 100000000) (460931 / 125000) (3687581 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2051 / 25600) (41021 / 512000) (460931 / 125000) (3687581 / 1000000) (32263 / 1000) (32269 / 1000)
    (24239 / 500) (48553 / 1000) (-551561 / 1000) (25281 / 62500) (2958601 / 1000) (62769 / 15625000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (460931 / 125000) (63725735733 / 1000000) (62769 / 15625000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (460931 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (460931 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell061 :
    ∀ t ∈ Set.Icc ((41021 / 512000) : ℝ) (20511 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173790529 / 1000000000) : ℝ) ≤ Real.exp (2 * (41021 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41021 / 512000)) (1173790529 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20511 / 256000) : ℝ)) ≤ (293448779 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20511 / 256000)) (293448779 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63728412269 / 1000000) : ℝ) ≤ Real.exp (3 * (1843731 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1843731 / 500000)) (63728412269 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41021 / 512000) : ℝ) (20511 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1843731 / 500000) (737519 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41021 / 512000) (20511 / 256000) (1173790529 / 1000000000) (293448779 / 250000000) (1843731 / 500000) (737519 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41021 / 512000) (20511 / 256000) (1843731 / 500000) (737519 / 200000) (32263 / 1000) (32269 / 1000)
    (48479 / 1000) (9711 / 200) (-137891 / 250) (101121 / 250000) (591729 / 200) (4017047 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1843731 / 500000) (63728412269 / 1000000) (4017047 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843731 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843731 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell062 :
    ∀ t ∈ Set.Icc ((20511 / 256000) : ℝ) (41023 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((234759023 / 200000000) : ℝ) ≤ Real.exp (2 * (20511 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20511 / 256000)) (234759023 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41023 / 512000) : ℝ)) ≤ (1173799701 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41023 / 512000)) (1173799701 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63731280111 / 1000000) : ℝ) ≤ Real.exp (3 * (3687477 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3687477 / 1000000)) (63731280111 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20511 / 256000) : ℝ) (41023 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3687477 / 1000000) (368761 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20511 / 256000) (41023 / 512000) (234759023 / 200000000) (1173799701 / 1000000000) (3687477 / 1000000) (368761 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20511 / 256000) (41023 / 512000) (3687477 / 1000000) (368761 / 100000) (4033 / 125) (3227 / 100)
    (48481 / 1000) (48557 / 1000) (-551567 / 1000) (40447 / 100000) (1479347 / 500) (2008433 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3687477 / 1000000) (63731280111 / 1000000) (2008433 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687477 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687477 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell063 :
    ∀ t ∈ Set.Icc ((41023 / 512000) : ℝ) (641 / 8000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((11737997 / 10000000) : ℝ) ≤ Real.exp (2 * (41023 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41023 / 512000)) (11737997 / 10000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((641 / 8000) : ℝ)) ≤ (586902143 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (641 / 8000)) (586902143 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63733956879 / 1000000) : ℝ) ≤ Real.exp (3 * (3687491 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3687491 / 1000000)) (63733956879 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41023 / 512000) : ℝ) (641 / 8000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3687491 / 1000000) (460953 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41023 / 512000) (641 / 8000) (11737997 / 10000000) (586902143 / 500000000) (3687491 / 1000000) (460953 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41023 / 512000) (641 / 8000) (3687491 / 1000000) (460953 / 125000) (4033 / 125) (3227 / 100)
    (48483 / 1000) (24279 / 500) (-551569 / 1000) (202229 / 500000) (2958739 / 1000) (2008349 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3687491 / 1000000) (63733956879 / 1000000) (2008349 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687491 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687491 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell064 :
    ∀ t ∈ Set.Icc ((641 / 8000) : ℝ) (1641 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((234760857 / 200000000) : ℝ) ≤ Real.exp (2 * (641 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (641 / 8000)) (234760857 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1641 / 20480) : ℝ)) ≤ (1173808871 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1641 / 20480)) (1173808871 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63736824971 / 1000000) : ℝ) ≤ Real.exp (3 * (1843753 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1843753 / 500000)) (63736824971 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((641 / 8000) : ℝ) (1641 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1843753 / 500000) (1843819 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (641 / 8000) (1641 / 20480) (234760857 / 200000000) (1173808871 / 1000000000) (1843753 / 500000) (1843819 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (641 / 8000) (1641 / 20480) (1843753 / 500000) (1843819 / 500000) (4033 / 125) (3227 / 100)
    (9697 / 200) (1214 / 25) (-68947 / 125) (101111 / 250000) (2958783 / 1000) (4016517 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1843753 / 500000) (63736824971 / 1000000) (4016517 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843753 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843753 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell065 :
    ∀ t ∈ Set.Icc ((1641 / 20480) : ℝ) (20513 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((117380887 / 100000000) : ℝ) ≤ Real.exp (2 * (1641 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1641 / 20480)) (117380887 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20513 / 256000) : ℝ)) ≤ (73363341 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20513 / 256000)) (73363341 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15934875493 / 250000) : ℝ) ≤ Real.exp (3 * (23047 / 6250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (23047 / 6250)) (15934875493 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1641 / 20480) : ℝ) (20513 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (23047 / 6250) (3687653 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1641 / 20480) (20513 / 256000) (117380887 / 100000000) (73363341 / 62500000) (23047 / 6250) (3687653 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1641 / 20480) (20513 / 256000) (23047 / 6250) (3687653 / 1000000) (6453 / 200) (32271 / 1000)
    (24243 / 500) (24281 / 500) (-275787 / 500) (25277 / 62500) (369854 / 125) (1004087 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (23047 / 6250) (15934875493 / 250000) (1004087 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (23047 / 6250)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (23047 / 6250)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell066 :
    ∀ t ∈ Set.Icc ((20513 / 256000) : ℝ) (41027 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((234762691 / 200000000) : ℝ) ≤ Real.exp (2 * (20513 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20513 / 256000)) (234762691 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41027 / 512000) : ℝ)) ≤ (1173818041 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41027 / 512000)) (1173818041 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63742179087 / 1000000) : ℝ) ≤ Real.exp (3 * (1843767 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1843767 / 500000)) (63742179087 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20513 / 256000) : ℝ) (41027 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1843767 / 500000) (3687667 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20513 / 256000) (41027 / 512000) (234762691 / 200000000) (1173818041 / 1000000000) (1843767 / 500000) (3687667 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20513 / 256000) (41027 / 512000) (1843767 / 500000) (3687667 / 1000000) (6453 / 200) (32271 / 1000)
    (6061 / 125) (12141 / 250) (-551577 / 1000) (20221 / 50000) (2958877 / 1000) (4016179 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1843767 / 500000) (63742179087 / 1000000) (4016179 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843767 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843767 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell067 :
    ∀ t ∈ Set.Icc ((41027 / 512000) : ℝ) (10257 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((29345451 / 25000000) : ℝ) ≤ Real.exp (2 * (41027 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41027 / 512000)) (29345451 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((10257 / 128000) : ℝ)) ≤ (1173822627 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (10257 / 128000)) (1173822627 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15936261887 / 250000) : ℝ) ≤ Real.exp (3 * (3687549 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3687549 / 1000000)) (15936261887 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41027 / 512000) : ℝ) (10257 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3687549 / 1000000) (1843841 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41027 / 512000) (10257 / 128000) (29345451 / 25000000) (1173822627 / 1000000000) (3687549 / 1000000) (1843841 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41027 / 512000) (10257 / 128000) (3687549 / 1000000) (1843841 / 500000) (6453 / 200) (32271 / 1000)
    (4849 / 100) (9713 / 200) (-27579 / 50) (404407 / 1000000) (118357 / 40) (4015999 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3687549 / 1000000) (15936261887 / 250000) (4015999 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687549 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687549 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell068 :
    ∀ t ∈ Set.Icc ((10257 / 128000) : ℝ) (41029 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((586911313 / 500000000) : ℝ) ≤ Real.exp (2 * (10257 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (10257 / 128000)) (586911313 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41029 / 512000) : ℝ)) ≤ (293456803 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41029 / 512000)) (293456803 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((12749544979 / 200000) : ℝ) ≤ Real.exp (3 * (3687563 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3687563 / 1000000)) (12749544979 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((10257 / 128000) : ℝ) (41029 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3687563 / 1000000) (230481 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (10257 / 128000) (41029 / 512000) (586911313 / 500000000) (293456803 / 250000000) (3687563 / 1000000) (230481 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (10257 / 128000) (41029 / 512000) (3687563 / 1000000) (230481 / 62500) (16133 / 500) (4034 / 125)
    (48491 / 1000) (48567 / 1000) (-275791 / 500) (202197 / 500000) (295897 / 100) (401583 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3687563 / 1000000) (12749544979 / 200000) (401583 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687563 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687563 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell069 :
    ∀ t ∈ Set.Icc ((41029 / 512000) : ℝ) (4103 / 51200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173827211 / 1000000000) : ℝ) ≤ Real.exp (2 * (41029 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41029 / 512000)) (1173827211 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4103 / 51200) : ℝ)) ≤ (1173831797 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4103 / 51200)) (1173831797 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31875296803 / 500000) : ℝ) ≤ Real.exp (3 * (1843789 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1843789 / 500000)) (31875296803 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41029 / 512000) : ℝ) (4103 / 51200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1843789 / 500000) (368771 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41029 / 512000) (4103 / 51200) (1173827211 / 1000000000) (1173831797 / 1000000000) (1843789 / 500000) (368771 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41029 / 512000) (4103 / 51200) (1843789 / 500000) (368771 / 100000) (16133 / 500) (4034 / 125)
    (48493 / 1000) (48569 / 1000) (-551589 / 1000) (404381 / 1000000) (591803 / 200) (4015649 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1843789 / 500000) (31875296803 / 500000) (4015649 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843789 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843789 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell070 :
    ∀ t ∈ Set.Icc ((4103 / 51200) : ℝ) (41031 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293457949 / 250000000) : ℝ) ≤ Real.exp (2 * (4103 / 51200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4103 / 51200)) (293457949 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41031 / 512000) : ℝ)) ≤ (1173836383 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41031 / 512000)) (1173836383 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31876635593 / 500000) : ℝ) ≤ Real.exp (3 * (460949 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (460949 / 125000)) (31876635593 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4103 / 51200) : ℝ) (41031 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (460949 / 125000) (147509 / 40000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (4103 / 51200) (41031 / 512000) (293457949 / 250000000) (1173836383 / 1000000000) (460949 / 125000) (147509 / 40000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (4103 / 51200) (41031 / 512000) (460949 / 125000) (147509 / 40000) (16133 / 500) (4034 / 125)
    (9699 / 200) (48571 / 1000) (-551587 / 1000) (404369 / 1000000) (2959063 / 1000) (4015481 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (460949 / 125000) (31876635593 / 500000) (4015481 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (460949 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (460949 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell071 :
    ∀ t ∈ Set.Icc ((41031 / 512000) : ℝ) (5129 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((586918191 / 500000000) : ℝ) ≤ Real.exp (2 * (41031 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41031 / 512000)) (586918191 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((5129 / 64000) : ℝ)) ≤ (146730121 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (5129 / 64000)) (146730121 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31877974439 / 500000) : ℝ) ≤ Real.exp (3 * (1843803 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1843803 / 500000)) (31877974439 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41031 / 512000) : ℝ) (5129 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1843803 / 500000) (3687739 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41031 / 512000) (5129 / 64000) (586918191 / 500000000) (146730121 / 125000000) (1843803 / 500000) (3687739 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41031 / 512000) (5129 / 64000) (1843803 / 500000) (3687739 / 1000000) (32267 / 1000) (32273 / 1000)
    (6062 / 125) (12143 / 250) (-55159 / 100) (101089 / 250000) (739777 / 250) (250957 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1843803 / 500000) (31877974439 / 500000) (250957 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843803 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843803 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell072 :
    ∀ t ∈ Set.Icc ((5129 / 64000) : ℝ) (41033 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173840967 / 1000000000) : ℝ) ≤ Real.exp (2 * (5129 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (5129 / 64000)) (1173840967 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41033 / 512000) : ℝ)) ≤ (1173845553 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41033 / 512000)) (1173845553 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63758817959 / 1000000) : ℝ) ≤ Real.exp (3 * (3687621 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3687621 / 1000000)) (63758817959 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((5129 / 64000) : ℝ) (41033 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3687621 / 1000000) (1843877 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (5129 / 64000) (41033 / 512000) (1173840967 / 1000000000) (1173845553 / 1000000000) (3687621 / 1000000) (1843877 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (5129 / 64000) (41033 / 512000) (3687621 / 1000000) (1843877 / 500000) (32267 / 1000) (32273 / 1000)
    (24249 / 500) (24287 / 500) (-551593 / 1000) (404343 / 1000000) (739789 / 250) (4015131 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3687621 / 1000000) (63758817959 / 1000000) (4015131 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687621 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687621 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell073 :
    ∀ t ∈ Set.Icc ((41033 / 512000) : ℝ) (20517 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((73365347 / 62500000) : ℝ) ≤ Real.exp (2 * (41033 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41033 / 512000)) (73365347 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20517 / 256000) : ℝ)) ≤ (1173850139 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20517 / 256000)) (1173850139 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((12752299177 / 200000) : ℝ) ≤ Real.exp (3 * (737527 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (737527 / 200000)) (12752299177 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41033 / 512000) : ℝ) (20517 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (737527 / 200000) (460971 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41033 / 512000) (20517 / 256000) (73365347 / 62500000) (1173850139 / 1000000000) (737527 / 200000) (460971 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41033 / 512000) (20517 / 256000) (737527 / 200000) (460971 / 125000) (32267 / 1000) (32273 / 1000)
    (97 / 2) (6072 / 125) (-110319 / 200) (404331 / 1000000) (2959201 / 1000) (4014963 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (737527 / 200000) (12752299177 / 200000) (4014963 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (737527 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (737527 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell074 :
    ∀ t ∈ Set.Icc ((20517 / 256000) : ℝ) (8207 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((586925069 / 500000000) : ℝ) ≤ Real.exp (2 * (20517 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20517 / 256000)) (586925069 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8207 / 102400) : ℝ)) ≤ (293463681 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8207 / 102400)) (293463681 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((12752873043 / 200000) : ℝ) ≤ Real.exp (3 * (73753 / 20000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (73753 / 20000)) (12752873043 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20517 / 256000) : ℝ) (8207 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (73753 / 20000) (3687783 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20517 / 256000) (8207 / 102400) (586925069 / 500000000) (293463681 / 250000000) (73753 / 20000) (3687783 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20517 / 256000) (8207 / 102400) (73753 / 20000) (3687783 / 1000000) (8067 / 250) (16137 / 500)
    (24251 / 500) (24289 / 500) (-275799 / 500) (404317 / 1000000) (2959249 / 1000) (2007391 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (73753 / 20000) (12752873043 / 200000) (2007391 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (73753 / 20000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (73753 / 20000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell075 :
    ∀ t ∈ Set.Icc ((8207 / 102400) : ℝ) (10259 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173854723 / 1000000000) : ℝ) ≤ Real.exp (2 * (8207 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8207 / 102400)) (1173854723 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((10259 / 128000) : ℝ)) ≤ (1173859309 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (10259 / 128000)) (1173859309 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31883521687 / 500000) : ℝ) ≤ Real.exp (3 * (230479 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (230479 / 62500)) (31883521687 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8207 / 102400) : ℝ) (10259 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (230479 / 62500) (3687797 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8207 / 102400) (10259 / 128000) (1173854723 / 1000000000) (1173859309 / 1000000000) (230479 / 62500) (3687797 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8207 / 102400) (10259 / 128000) (230479 / 62500) (3687797 / 1000000) (8067 / 250) (16137 / 500)
    (48503 / 1000) (48579 / 1000) (-2758 / 5) (80861 / 200000) (1479647 / 500) (4014613 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (230479 / 62500) (31883521687 / 500000) (4014613 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (230479 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (230479 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell076 :
    ∀ t ∈ Set.Icc ((10259 / 128000) : ℝ) (41037 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293464827 / 250000000) : ℝ) ≤ Real.exp (2 * (10259 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (10259 / 128000)) (293464827 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41037 / 512000) : ℝ)) ≤ (234772779 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41037 / 512000)) (234772779 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31884956477 / 500000) : ℝ) ≤ Real.exp (3 * (3687679 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3687679 / 1000000)) (31884956477 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((10259 / 128000) : ℝ) (41037 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3687679 / 1000000) (3687811 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (10259 / 128000) (41037 / 512000) (293464827 / 250000000) (234772779 / 200000000) (3687679 / 1000000) (3687811 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (10259 / 128000) (41037 / 512000) (3687679 / 1000000) (3687811 / 1000000) (32269 / 1000) (16137 / 500)
    (9701 / 200) (48581 / 1000) (-551607 / 1000) (404291 / 1000000) (2959339 / 1000) (4014433 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3687679 / 1000000) (31884956477 / 500000) (4014433 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687679 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687679 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell077 :
    ∀ t ∈ Set.Icc ((41037 / 512000) : ℝ) (20519 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((586931947 / 500000000) : ℝ) ≤ Real.exp (2 * (41037 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41037 / 512000)) (586931947 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20519 / 256000) : ℝ)) ≤ (3668339 / 3125000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20519 / 256000)) (3668339 / 3125000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((12754518269 / 200000) : ℝ) ≤ Real.exp (3 * (3687693 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3687693 / 1000000)) (12754518269 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41037 / 512000) : ℝ) (20519 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3687693 / 1000000) (1843913 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41037 / 512000) (20519 / 256000) (586931947 / 500000000) (3668339 / 3125000) (3687693 / 1000000) (1843913 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41037 / 512000) (20519 / 256000) (3687693 / 1000000) (1843913 / 500000) (32269 / 1000) (1291 / 40)
    (48507 / 1000) (48583 / 1000) (-110321 / 200) (404279 / 1000000) (2959387 / 1000) (501783 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3687693 / 1000000) (12754518269 / 200000) (501783 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687693 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687693 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell078 :
    ∀ t ∈ Set.Icc ((20519 / 256000) : ℝ) (41039 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173868479 / 1000000000) : ℝ) ≤ Real.exp (2 * (20519 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20519 / 256000)) (1173868479 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41039 / 512000) : ℝ)) ≤ (234774613 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41039 / 512000)) (234774613 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63775269849 / 1000000) : ℝ) ≤ Real.exp (3 * (3687707 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3687707 / 1000000)) (63775269849 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20519 / 256000) : ℝ) (41039 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3687707 / 1000000) (23049 / 6250) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20519 / 256000) (41039 / 512000) (1173868479 / 1000000000) (234774613 / 200000000) (3687707 / 1000000) (23049 / 6250) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20519 / 256000) (41039 / 512000) (3687707 / 1000000) (23049 / 6250) (32269 / 1000) (1291 / 40)
    (48509 / 1000) (6073 / 125) (-68951 / 125) (404267 / 1000000) (369929 / 125) (250881 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3687707 / 1000000) (63775269849 / 1000000) (250881 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687707 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687707 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell079 :
    ∀ t ∈ Set.Icc ((41039 / 512000) : ℝ) (513 / 6400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((146734133 / 125000000) : ℝ) ≤ Real.exp (2 * (41039 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41039 / 512000)) (146734133 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((513 / 6400) : ℝ)) ≤ (1173877651 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (513 / 6400)) (1173877651 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((318890699 / 5000) : ℝ) ≤ Real.exp (3 * (1843861 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1843861 / 500000)) (318890699 / 5000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41039 / 512000) : ℝ) (513 / 6400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1843861 / 500000) (737571 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41039 / 512000) (513 / 6400) (146734133 / 125000000) (1173877651 / 1000000000) (1843861 / 500000) (737571 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41039 / 512000) (513 / 6400) (1843861 / 500000) (737571 / 200000) (3227 / 100) (1291 / 40)
    (4851 / 100) (24293 / 500) (-551611 / 1000) (202127 / 500000) (73987 / 25) (802783 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1843861 / 500000) (318890699 / 5000) (802783 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843861 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843861 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch003 :
    ∀ t ∈ Set.Icc ((2051 / 25600) : ℝ) (513 / 6400),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell060
      hpThetaDensityLowerExpCompact_cell061)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell062
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell063
      hpThetaDensityLowerExpCompact_cell064)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell065
      hpThetaDensityLowerExpCompact_cell066)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell067
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell068
      hpThetaDensityLowerExpCompact_cell069))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell070
      hpThetaDensityLowerExpCompact_cell071)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell072
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell073
      hpThetaDensityLowerExpCompact_cell074)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell075
      hpThetaDensityLowerExpCompact_cell076)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell077
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell078
      hpThetaDensityLowerExpCompact_cell079)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch003
end HodgeProofHP
