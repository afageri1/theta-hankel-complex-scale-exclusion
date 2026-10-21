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
theorem hpThetaDensityLowerExpCompact_cell040 :
    ∀ t ∈ Set.Icc ((41 / 512) : ℝ) (41001 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((586847123 / 500000000) : ℝ) ≤ Real.exp (2 * (41 / 512)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41 / 512)) (586847123 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41001 / 512000) : ℝ)) ≤ (73356177 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41001 / 512000)) (73356177 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((127341401 / 2000) : ℝ) ≤ Real.exp (3 * (92179 / 25000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (92179 / 25000)) (127341401 / 2000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41 / 512) : ℝ) (41001 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (92179 / 25000) (3687293 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41 / 512) (41001 / 512000) (586847123 / 500000000) (73356177 / 62500000) (92179 / 25000) (3687293 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41 / 512) (41001 / 512000) (92179 / 25000) (3687293 / 1000000) (4032 / 125) (16131 / 500)
    (48443 / 1000) (48519 / 1000) (-55151 / 100) (404751 / 1000000) (739419 / 250) (251293 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (92179 / 25000) (127341401 / 2000) (251293 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (92179 / 25000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (92179 / 25000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell041 :
    ∀ t ∈ Set.Icc ((41001 / 512000) : ℝ) (20501 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173698831 / 1000000000) : ℝ) ≤ Real.exp (2 * (41001 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41001 / 512000)) (1173698831 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20501 / 256000) : ℝ)) ≤ (146712927 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20501 / 256000)) (146712927 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15918343681 / 250000) : ℝ) ≤ Real.exp (3 * (1843587 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1843587 / 500000)) (15918343681 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41001 / 512000) : ℝ) (20501 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1843587 / 500000) (3687307 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41001 / 512000) (20501 / 256000) (1173698831 / 1000000000) (146712927 / 125000000) (1843587 / 500000) (3687307 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41001 / 512000) (20501 / 256000) (1843587 / 500000) (3687307 / 1000000) (32257 / 1000) (16131 / 500)
    (9689 / 200) (1213 / 25) (-68939 / 125) (202369 / 500000) (2957721 / 1000) (4020519 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1843587 / 500000) (15918343681 / 250000) (4020519 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843587 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843587 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell042 :
    ∀ t ∈ Set.Icc ((20501 / 256000) : ℝ) (41003 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((234740683 / 200000000) : ℝ) ≤ Real.exp (2 * (20501 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20501 / 256000)) (234740683 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41003 / 512000) : ℝ)) ≤ (1173708001 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41003 / 512000)) (1173708001 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63676240089 / 1000000) : ℝ) ≤ Real.exp (3 * (3687189 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3687189 / 1000000)) (63676240089 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20501 / 256000) : ℝ) (41003 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3687189 / 1000000) (1843661 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20501 / 256000) (41003 / 512000) (234740683 / 200000000) (1173708001 / 1000000000) (3687189 / 1000000) (1843661 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20501 / 256000) (41003 / 512000) (3687189 / 1000000) (1843661 / 500000) (32257 / 1000) (32263 / 1000)
    (24223 / 500) (24261 / 500) (-110303 / 200) (16189 / 40000) (2957769 / 1000) (2010169 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3687189 / 1000000) (63676240089 / 1000000) (2010169 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687189 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687189 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell043 :
    ∀ t ∈ Set.Icc ((41003 / 512000) : ℝ) (10251 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293427 / 250000) : ℝ) ≤ Real.exp (2 * (41003 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41003 / 512000)) (293427 / 250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((10251 / 128000) : ℝ)) ≤ (586856293 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (10251 / 128000)) (586856293 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31839457273 / 500000) : ℝ) ≤ Real.exp (3 * (3687203 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3687203 / 1000000)) (31839457273 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41003 / 512000) : ℝ) (10251 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3687203 / 1000000) (460917 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41003 / 512000) (10251 / 128000) (293427 / 250000) (586856293 / 500000000) (3687203 / 1000000) (460917 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41003 / 512000) (10251 / 128000) (3687203 / 1000000) (460917 / 125000) (32257 / 1000) (32263 / 1000)
    (6056 / 125) (12131 / 250) (-551517 / 1000) (404713 / 1000000) (1478907 / 500) (402017 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3687203 / 1000000) (31839457273 / 500000) (402017 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687203 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687203 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell044 :
    ∀ t ∈ Set.Icc ((10251 / 128000) : ℝ) (8201 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((234742517 / 200000000) : ℝ) ≤ Real.exp (2 * (10251 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (10251 / 128000)) (234742517 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8201 / 102400) : ℝ)) ≤ (1173717171 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8201 / 102400)) (1173717171 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63681780161 / 1000000) : ℝ) ≤ Real.exp (3 * (1843609 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1843609 / 500000)) (63681780161 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((10251 / 128000) : ℝ) (8201 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1843609 / 500000) (73747 / 20000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (10251 / 128000) (8201 / 102400) (234742517 / 200000000) (1173717171 / 1000000000) (1843609 / 500000) (73747 / 20000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (10251 / 128000) (8201 / 102400) (1843609 / 500000) (73747 / 20000) (16129 / 500) (32263 / 1000)
    (969 / 20) (1941 / 40) (-137881 / 250) (404699 / 1000000) (2957859 / 1000) (4019989 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1843609 / 500000) (63681780161 / 1000000) (4019989 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843609 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843609 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell045 :
    ∀ t ∈ Set.Icc ((8201 / 102400) : ℝ) (20503 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((117371717 / 100000000) : ℝ) ≤ Real.exp (2 * (8201 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8201 / 102400)) (117371717 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20503 / 256000) : ℝ)) ≤ (293430439 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20503 / 256000)) (293430439 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1273689097 / 20000) : ℝ) ≤ Real.exp (3 * (57613 / 15625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (57613 / 15625)) (1273689097 / 20000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8201 / 102400) : ℝ) (20503 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (57613 / 15625) (737473 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8201 / 102400) (20503 / 256000) (117371717 / 100000000) (293430439 / 250000000) (57613 / 15625) (737473 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8201 / 102400) (20503 / 256000) (57613 / 15625) (737473 / 200000) (16129 / 500) (4033 / 125)
    (12113 / 250) (48527 / 1000) (-275761 / 500) (404687 / 1000000) (2957907 / 1000) (200991 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (57613 / 15625) (1273689097 / 20000) (200991 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (57613 / 15625)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (57613 / 15625)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell046 :
    ∀ t ∈ Set.Icc ((20503 / 256000) : ℝ) (41007 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((234744351 / 200000000) : ℝ) ≤ Real.exp (2 * (20503 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20503 / 256000)) (234744351 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41007 / 512000) : ℝ)) ≤ (1173726341 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41007 / 512000)) (1173726341 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63687129653 / 1000000) : ℝ) ≤ Real.exp (3 * (1843623 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1843623 / 500000)) (63687129653 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20503 / 256000) : ℝ) (41007 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1843623 / 500000) (3687379 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20503 / 256000) (41007 / 512000) (234744351 / 200000000) (1173726341 / 1000000000) (1843623 / 500000) (3687379 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20503 / 256000) (41007 / 512000) (1843623 / 500000) (3687379 / 1000000) (16129 / 500) (4033 / 125)
    (48453 / 1000) (48529 / 1000) (-22061 / 40) (16187 / 40000) (369744 / 125) (4019651 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1843623 / 500000) (63687129653 / 1000000) (4019651 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843623 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843623 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell047 :
    ∀ t ∈ Set.Icc ((41007 / 512000) : ℝ) (2563 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((58686317 / 50000000) : ℝ) ≤ Real.exp (2 * (41007 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41007 / 512000)) (58686317 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2563 / 32000) : ℝ)) ≤ (46949237 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2563 / 32000)) (46949237 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63689995637 / 1000000) : ℝ) ≤ Real.exp (3 * (3687261 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3687261 / 1000000)) (63689995637 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41007 / 512000) : ℝ) (2563 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3687261 / 1000000) (1843697 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41007 / 512000) (2563 / 32000) (58686317 / 50000000) (46949237 / 40000000) (3687261 / 1000000) (1843697 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41007 / 512000) (2563 / 32000) (3687261 / 1000000) (1843697 / 500000) (32259 / 1000) (4033 / 125)
    (9691 / 200) (48531 / 1000) (-68941 / 125) (404661 / 1000000) (2958) (401947 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3687261 / 1000000) (63689995637 / 1000000) (401947 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687261 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687261 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell048 :
    ∀ t ∈ Set.Icc ((2563 / 32000) : ℝ) (41009 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293432731 / 250000000) : ℝ) ≤ Real.exp (2 * (2563 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2563 / 32000)) (293432731 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41009 / 512000) : ℝ)) ≤ (117373551 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41009 / 512000)) (117373551 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63692670671 / 1000000) : ℝ) ≤ Real.exp (3 * (147491 / 40000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (147491 / 40000)) (63692670671 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2563 / 32000) : ℝ) (41009 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (147491 / 40000) (230463 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2563 / 32000) (41009 / 512000) (293432731 / 250000000) (117373551 / 100000000) (147491 / 40000) (230463 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2563 / 32000) (41009 / 512000) (147491 / 40000) (230463 / 62500) (32259 / 1000) (6453 / 200)
    (48457 / 1000) (48533 / 1000) (-55153 / 100) (404649 / 1000000) (591609 / 200) (4019301 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (147491 / 40000) (63692670671 / 1000000) (4019301 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (147491 / 40000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (147491 / 40000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell049 :
    ∀ t ∈ Set.Icc ((41009 / 512000) : ℝ) (4101 / 51200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173735509 / 1000000000) : ℝ) ≤ Real.exp (2 * (41009 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41009 / 512000)) (1173735509 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4101 / 51200) : ℝ)) ≤ (234748019 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4101 / 51200)) (234748019 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((12739107381 / 200000) : ℝ) ≤ Real.exp (3 * (368729 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (368729 / 100000)) (12739107381 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41009 / 512000) : ℝ) (4101 / 51200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (368729 / 100000) (1843711 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41009 / 512000) (4101 / 51200) (1173735509 / 1000000000) (234748019 / 200000000) (368729 / 100000) (1843711 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41009 / 512000) (4101 / 51200) (368729 / 100000) (1843711 / 500000) (32259 / 1000) (6453 / 200)
    (48459 / 1000) (24267 / 500) (-551537 / 1000) (80927 / 200000) (295809 / 100) (50239 / 12500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (368729 / 100000) (12739107381 / 200000) (50239 / 12500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (368729 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (368729 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell050 :
    ∀ t ∈ Set.Icc ((4101 / 51200) : ℝ) (41011 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((586870047 / 500000000) : ℝ) ≤ Real.exp (2 * (4101 / 51200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4101 / 51200)) (586870047 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41011 / 512000) : ℝ)) ≤ (29343617 / 25000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41011 / 512000)) (29343617 / 25000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15924553043 / 250000) : ℝ) ≤ Real.exp (3 * (460913 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (460913 / 125000)) (15924553043 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4101 / 51200) : ℝ) (41011 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (460913 / 125000) (3687437 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (4101 / 51200) (41011 / 512000) (586870047 / 500000000) (29343617 / 25000000) (460913 / 125000) (3687437 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (4101 / 51200) (41011 / 512000) (460913 / 125000) (3687437 / 1000000) (1613 / 50) (6453 / 200)
    (2423 / 50) (6067 / 125) (-110307 / 200) (404623 / 1000000) (1479069 / 500) (502369 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (460913 / 125000) (15924553043 / 250000) (502369 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (460913 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (460913 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell051 :
    ∀ t ∈ Set.Icc ((41011 / 512000) : ℝ) (10253 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173744679 / 1000000000) : ℝ) ≤ Real.exp (2 * (41011 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41011 / 512000)) (1173744679 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((10253 / 128000) : ℝ)) ≤ (234749853 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (10253 / 128000)) (234749853 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((995326368 / 15625) : ℝ) ≤ Real.exp (3 * (1843659 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1843659 / 500000)) (995326368 / 15625) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41011 / 512000) : ℝ) (10253 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1843659 / 500000) (3687451 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41011 / 512000) (10253 / 128000) (1173744679 / 1000000000) (234749853 / 200000000) (1843659 / 500000) (3687451 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41011 / 512000) (10253 / 128000) (1843659 / 500000) (3687451 / 1000000) (1613 / 50) (16133 / 500)
    (24231 / 500) (24269 / 500) (-275769 / 500) (404611 / 1000000) (2958183 / 1000) (4018783 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1843659 / 500000) (995326368 / 15625) (4018783 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843659 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843659 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell052 :
    ∀ t ∈ Set.Icc ((10253 / 128000) : ℝ) (41013 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((73359329 / 62500000) : ℝ) ≤ Real.exp (2 * (10253 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (10253 / 128000)) (73359329 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41013 / 512000) : ℝ)) ≤ (23475077 / 20000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41013 / 512000)) (23475077 / 20000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15925938539 / 250000) : ℝ) ≤ Real.exp (3 * (3687333 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3687333 / 1000000)) (15925938539 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((10253 / 128000) : ℝ) (41013 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3687333 / 1000000) (1843733 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (10253 / 128000) (41013 / 512000) (73359329 / 62500000) (23475077 / 20000000) (3687333 / 1000000) (1843733 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (10253 / 128000) (41013 / 512000) (3687333 / 1000000) (1843733 / 500000) (1613 / 50) (16133 / 500)
    (6058 / 125) (2427 / 50) (-551541 / 1000) (202299 / 500000) (2958231 / 1000) (2009301 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3687333 / 1000000) (15925938539 / 250000) (2009301 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687333 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687333 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell053 :
    ∀ t ∈ Set.Icc ((41013 / 512000) : ℝ) (20507 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173753849 / 1000000000) : ℝ) ≤ Real.exp (2 * (41013 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41013 / 512000)) (1173753849 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20507 / 256000) : ℝ)) ≤ (234751687 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20507 / 256000)) (234751687 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((7963303721 / 125000) : ℝ) ≤ Real.exp (3 * (3687347 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3687347 / 1000000)) (7963303721 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41013 / 512000) : ℝ) (20507 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3687347 / 1000000) (92187 / 25000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41013 / 512000) (20507 / 256000) (1173753849 / 1000000000) (234751687 / 200000000) (3687347 / 1000000) (92187 / 25000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41013 / 512000) (20507 / 256000) (3687347 / 1000000) (92187 / 25000) (32261 / 1000) (16133 / 500)
    (9693 / 200) (48541 / 1000) (-551543 / 1000) (80917 / 200000) (739569 / 250) (4018433 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3687347 / 1000000) (7963303721 / 125000) (4018433 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687347 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687347 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell054 :
    ∀ t ∈ Set.Icc ((20507 / 256000) : ℝ) (8203 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((586879217 / 500000000) : ℝ) ≤ Real.exp (2 * (20507 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20507 / 256000)) (586879217 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8203 / 102400) : ℝ)) ≤ (58688151 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8203 / 102400)) (58688151 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63709296621 / 1000000) : ℝ) ≤ Real.exp (3 * (1843681 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1843681 / 500000)) (63709296621 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20507 / 256000) : ℝ) (8203 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1843681 / 500000) (1843747 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20507 / 256000) (8203 / 102400) (586879217 / 500000000) (58688151 / 50000000) (1843681 / 500000) (1843747 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20507 / 256000) (8203 / 102400) (1843681 / 500000) (1843747 / 500000) (32261 / 1000) (32267 / 1000)
    (48467 / 1000) (48543 / 1000) (-11031 / 20) (101143 / 250000) (2958321 / 1000) (1004563 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1843681 / 500000) (63709296621 / 1000000) (1004563 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843681 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843681 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell055 :
    ∀ t ∈ Set.Icc ((8203 / 102400) : ℝ) (5127 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173763019 / 1000000000) : ℝ) ≤ Real.exp (2 * (8203 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8203 / 102400)) (1173763019 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((5127 / 64000) : ℝ)) ≤ (234753521 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (5127 / 64000)) (234753521 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31855986233 / 500000) : ℝ) ≤ Real.exp (3 * (230461 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (230461 / 62500)) (31855986233 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8203 / 102400) : ℝ) (5127 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (230461 / 62500) (3687509 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8203 / 102400) (5127 / 64000) (1173763019 / 1000000000) (234753521 / 200000000) (230461 / 62500) (3687509 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8203 / 102400) (5127 / 64000) (230461 / 62500) (3687509 / 1000000) (32261 / 1000) (32267 / 1000)
    (48469 / 1000) (9709 / 200) (-137887 / 250) (5057 / 12500) (2958369 / 1000) (1004521 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (230461 / 62500) (31855986233 / 500000) (1004521 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (230461 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (230461 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell056 :
    ∀ t ∈ Set.Icc ((5127 / 64000) : ℝ) (41017 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293441901 / 250000000) : ℝ) ≤ Real.exp (2 * (5127 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (5127 / 64000)) (293441901 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41017 / 512000) : ℝ)) ≤ (117377219 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41017 / 512000)) (117377219 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((7964331053 / 125000) : ℝ) ≤ Real.exp (3 * (368739 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (368739 / 100000)) (7964331053 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((5127 / 64000) : ℝ) (41017 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (368739 / 100000) (3687523 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (5127 / 64000) (41017 / 512000) (293441901 / 250000000) (117377219 / 100000000) (368739 / 100000) (3687523 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (5127 / 64000) (41017 / 512000) (368739 / 100000) (3687523 / 1000000) (16131 / 500) (32267 / 1000)
    (48471 / 1000) (24273 / 500) (-551551 / 1000) (404547 / 1000000) (1479207 / 500) (803583 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (368739 / 100000) (7964331053 / 125000) (803583 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (368739 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (368739 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell057 :
    ∀ t ∈ Set.Icc ((41017 / 512000) : ℝ) (20509 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173772189 / 1000000000) : ℝ) ≤ Real.exp (2 * (41017 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41017 / 512000)) (1173772189 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20509 / 256000) : ℝ)) ≤ (46951071 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20509 / 256000)) (46951071 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63717515647 / 1000000) : ℝ) ≤ Real.exp (3 * (737481 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (737481 / 200000)) (63717515647 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41017 / 512000) : ℝ) (20509 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (737481 / 200000) (1843769 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41017 / 512000) (20509 / 256000) (1173772189 / 1000000000) (46951071 / 40000000) (737481 / 200000) (1843769 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41017 / 512000) (20509 / 256000) (737481 / 200000) (1843769 / 500000) (16131 / 500) (8067 / 250)
    (6059 / 125) (12137 / 250) (-275777 / 500) (202267 / 500000) (2958463 / 1000) (2008867 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (737481 / 200000) (63717515647 / 1000000) (2008867 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (737481 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (737481 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell058 :
    ∀ t ∈ Set.Icc ((20509 / 256000) : ℝ) (41019 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((586888387 / 500000000) : ℝ) ≤ Real.exp (2 * (20509 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20509 / 256000)) (586888387 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41019 / 512000) : ℝ)) ≤ (14672267 / 12500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41019 / 512000)) (14672267 / 12500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63720191837 / 1000000) : ℝ) ≤ Real.exp (3 * (3687419 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3687419 / 1000000)) (63720191837 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20509 / 256000) : ℝ) (41019 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3687419 / 1000000) (57618 / 15625) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20509 / 256000) (41019 / 512000) (586888387 / 500000000) (14672267 / 12500000) (3687419 / 1000000) (57618 / 15625) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20509 / 256000) (41019 / 512000) (3687419 / 1000000) (57618 / 15625) (16131 / 500) (8067 / 250)
    (24237 / 500) (971 / 20) (-137889 / 250) (202261 / 500000) (2958507 / 1000) (803513 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3687419 / 1000000) (63720191837 / 1000000) (803513 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687419 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687419 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell059 :
    ∀ t ∈ Set.Icc ((41019 / 512000) : ℝ) (2051 / 25600), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173781359 / 1000000000) : ℝ) ≤ Real.exp (2 * (41019 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41019 / 512000)) (1173781359 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2051 / 25600) : ℝ)) ≤ (234757189 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2051 / 25600)) (234757189 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63723059309 / 1000000) : ℝ) ≤ Real.exp (3 * (1843717 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1843717 / 500000)) (63723059309 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41019 / 512000) : ℝ) (2051 / 25600),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1843717 / 500000) (1843783 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41019 / 512000) (2051 / 25600) (1173781359 / 1000000000) (234757189 / 200000000) (1843717 / 500000) (1843783 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41019 / 512000) (2051 / 25600) (1843717 / 500000) (1843783 / 500000) (32263 / 1000) (8067 / 250)
    (12119 / 250) (48551 / 1000) (-551563 / 1000) (101127 / 250000) (369819 / 125) (803477 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1843717 / 500000) (63723059309 / 1000000) (803477 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843717 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843717 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch002 :
    ∀ t ∈ Set.Icc ((41 / 512) : ℝ) (2051 / 25600),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell040
      hpThetaDensityLowerExpCompact_cell041)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell042
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell043
      hpThetaDensityLowerExpCompact_cell044)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell045
      hpThetaDensityLowerExpCompact_cell046)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell047
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell048
      hpThetaDensityLowerExpCompact_cell049))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell050
      hpThetaDensityLowerExpCompact_cell051)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell052
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell053
      hpThetaDensityLowerExpCompact_cell054)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell055
      hpThetaDensityLowerExpCompact_cell056)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell057
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell058
      hpThetaDensityLowerExpCompact_cell059)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch002
end HodgeProofHP
