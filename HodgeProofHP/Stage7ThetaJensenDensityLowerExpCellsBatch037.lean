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
theorem hpThetaDensityLowerExpCompact_cell740 :
    ∀ t ∈ Set.Icc ((44387 / 512000) : ℝ) (44403 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((23786519 / 20000000) : ℝ) ≤ Real.exp (2 * (44387 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44387 / 512000)) (23786519 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44403 / 512000) : ℝ)) ≤ (1189400287 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44403 / 512000)) (1189400287 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((73776881413 / 1000000) : ℝ) ≤ Real.exp (3 * (3736267 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3736267 / 1000000)) (73776881413 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44387 / 512000) : ℝ) (44403 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3736267 / 1000000) (186831 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44387 / 512000) (44403 / 512000) (23786519 / 20000000) (1189400287 / 1000000000) (3736267 / 1000000) (186831 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44387 / 512000) (44403 / 512000) (3736267 / 1000000) (186831 / 50000) (33419 / 1000) (4179 / 125)
    (54431 / 1000) (27317 / 500) (-279389 / 500) (181757 / 500000) (3119147 / 1000) (1734961 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3736267 / 1000000) (73776881413 / 1000000) (1734961 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3736267 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3736267 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell741 :
    ∀ t ∈ Set.Icc ((44403 / 512000) : ℝ) (44419 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((594700143 / 500000000) : ℝ) ≤ Real.exp (2 * (44403 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44403 / 512000)) (594700143 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44419 / 512000) : ℝ)) ≤ (594737313 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44419 / 512000)) (594737313 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((18457117363 / 250000) : ℝ) ≤ Real.exp (3 * (7473 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (7473 / 2000)) (18457117363 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44403 / 512000) : ℝ) (44419 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (7473 / 2000) (1868427 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44403 / 512000) (44419 / 512000) (594700143 / 500000000) (594737313 / 500000000) (7473 / 2000) (1868427 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44403 / 512000) (44419 / 512000) (7473 / 2000) (1868427 / 500000) (4178 / 125) (16719 / 500)
    (2723 / 50) (6833 / 125) (-55881 / 100) (5677 / 15625) (389991 / 125) (1733749 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (7473 / 2000) (18457117363 / 250000) (1733749 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7473 / 2000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7473 / 2000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell742 :
    ∀ t ∈ Set.Icc ((44419 / 512000) : ℝ) (8887 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((9515797 / 8000000) : ℝ) ≤ Real.exp (2 * (44419 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44419 / 512000)) (9515797 / 8000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8887 / 102400) : ℝ)) ≤ (1189548971 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8887 / 102400)) (1189548971 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((18470078801 / 250000) : ℝ) ≤ Real.exp (3 * (1868367 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1868367 / 500000)) (18470078801 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44419 / 512000) : ℝ) (8887 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1868367 / 500000) (58392 / 15625) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44419 / 512000) (8887 / 102400) (9515797 / 8000000) (1189548971 / 1000000000) (1868367 / 500000) (58392 / 15625) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44419 / 512000) (8887 / 102400) (1868367 / 500000) (58392 / 15625) (3343 / 100) (33443 / 1000)
    (54489 / 1000) (27347 / 500) (-279423 / 500) (363141 / 1000000) (312071 / 100) (433133 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1868367 / 500000) (18470078801 / 250000) (433133 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1868367 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1868367 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell743 :
    ∀ t ∈ Set.Icc ((8887 / 102400) : ℝ) (44451 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((118954897 / 100000000) : ℝ) ≤ Real.exp (2 * (8887 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8887 / 102400)) (118954897 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44451 / 512000) : ℝ)) ≤ (29740583 / 25000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44451 / 512000)) (29740583 / 25000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((18483049341 / 250000) : ℝ) ≤ Real.exp (3 * (467121 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (467121 / 125000)) (18483049341 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8887 / 102400) : ℝ) (44451 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (467121 / 125000) (3737321 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8887 / 102400) (44451 / 512000) (118954897 / 100000000) (29740583 / 25000000) (467121 / 125000) (3737321 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8887 / 102400) (44451 / 512000) (467121 / 125000) (3737321 / 1000000) (6687 / 200) (33449 / 1000)
    (54519 / 1000) (54723 / 1000) (-558887 / 1000) (181477 / 500000) (390186 / 125) (3462633 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (467121 / 125000) (18483049341 / 250000) (3462633 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (467121 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (467121 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell744 :
    ∀ t ∈ Set.Icc ((44451 / 512000) : ℝ) (44467 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1189623319 / 1000000000) : ℝ) ≤ Real.exp (2 * (44451 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44451 / 512000)) (1189623319 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44467 / 512000) : ℝ)) ≤ (594848837 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44467 / 512000)) (594848837 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((73983894007 / 1000000) : ℝ) ≤ Real.exp (3 * (3737201 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3737201 / 1000000)) (73983894007 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44451 / 512000) : ℝ) (44467 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3737201 / 1000000) (747511 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44451 / 512000) (44467 / 512000) (1189623319 / 1000000000) (594848837 / 500000000) (3737201 / 1000000) (747511 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44451 / 512000) (44467 / 512000) (3737201 / 1000000) (747511 / 200000) (33441 / 1000) (6691 / 200)
    (13637 / 250) (6844 / 125) (-558919 / 1000) (362769 / 1000000) (312227 / 100) (3460213 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3737201 / 1000000) (73983894007 / 1000000) (3460213 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3737201 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3737201 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell745 :
    ∀ t ∈ Set.Icc ((44467 / 512000) : ℝ) (44483 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1189697673 / 1000000000) : ℝ) ≤ Real.exp (2 * (44467 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44467 / 512000)) (1189697673 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44483 / 512000) : ℝ)) ≤ (4647547 / 3906250) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44483 / 512000)) (4647547 / 3906250) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((14807169781 / 200000) : ℝ) ≤ Real.exp (3 * (747487 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (747487 / 200000)) (14807169781 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44467 / 512000) : ℝ) (44483 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (747487 / 200000) (934447 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44467 / 512000) (44483 / 512000) (1189697673 / 1000000000) (4647547 / 3906250) (747487 / 200000) (934447 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44467 / 512000) (44483 / 512000) (747487 / 200000) (934447 / 250000) (16723 / 500) (1673 / 50)
    (27289 / 500) (27391 / 500) (-13974 / 25) (181291 / 500000) (390381 / 125) (691557 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (747487 / 200000) (14807169781 / 200000) (691557 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (747487 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (747487 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell746 :
    ∀ t ∈ Set.Icc ((44483 / 512000) : ℝ) (44499 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1189772031 / 1000000000) : ℝ) ≤ Real.exp (2 * (44483 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44483 / 512000)) (1189772031 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44499 / 512000) : ℝ)) ≤ (237969279 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44499 / 512000)) (237969279 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2963504721 / 40000) : ℝ) ≤ Real.exp (3 * (934417 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (934417 / 250000)) (2963504721 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44483 / 512000) : ℝ) (44499 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (934417 / 250000) (1869011 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44483 / 512000) (44499 / 512000) (1189772031 / 1000000000) (237969279 / 200000000) (934417 / 250000) (1869011 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44483 / 512000) (44499 / 512000) (934417 / 250000) (1869011 / 500000) (8363 / 250) (16733 / 500)
    (54607 / 1000) (54811 / 1000) (-558991 / 1000) (362397 / 1000000) (3123831 / 1000) (3455369 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (934417 / 250000) (2963504721 / 40000) (3455369 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (934417 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (934417 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell747 :
    ∀ t ∈ Set.Icc ((44499 / 512000) : ℝ) (8903 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((594923197 / 500000000) : ℝ) ≤ Real.exp (2 * (44499 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44499 / 512000)) (594923197 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8903 / 102400) : ℝ)) ≤ (1189920763 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8903 / 102400)) (1189920763 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((74139645763 / 1000000) : ℝ) ≤ Real.exp (3 * (1868951 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1868951 / 500000)) (74139645763 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44499 / 512000) : ℝ) (8903 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1868951 / 500000) (233641 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44499 / 512000) (8903 / 102400) (594923197 / 500000000) (1189920763 / 1000000000) (1868951 / 500000) (233641 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44499 / 512000) (8903 / 102400) (1868951 / 500000) (233641 / 62500) (16729 / 500) (33471 / 1000)
    (13659 / 250) (54841 / 1000) (-139757 / 250) (36221 / 100000) (3124613 / 1000) (215809 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1868951 / 500000) (74139645763 / 1000000) (215809 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1868951 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1868951 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell748 :
    ∀ t ∈ Set.Icc ((8903 / 102400) : ℝ) (44531 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((594960381 / 500000000) : ℝ) ≤ Real.exp (2 * (8903 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8903 / 102400)) (594960381 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44531 / 512000) : ℝ)) ≤ (237999027 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44531 / 512000)) (237999027 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((74191710037 / 1000000) : ℝ) ≤ Real.exp (3 * (467267 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (467267 / 125000)) (74191710037 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8903 / 102400) : ℝ) (44531 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (467267 / 125000) (3738489 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8903 / 102400) (44531 / 512000) (594960381 / 500000000) (237999027 / 200000000) (467267 / 125000) (3738489 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8903 / 102400) (44531 / 512000) (467267 / 125000) (3738489 / 1000000) (33463 / 1000) (33477 / 1000)
    (27333 / 500) (5487 / 100) (-139767 / 250) (45253 / 125000) (390674 / 125) (3450521 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (467267 / 125000) (74191710037 / 1000000) (3450521 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (467267 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (467267 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell749 :
    ∀ t ∈ Set.Icc ((44531 / 512000) : ℝ) (44547 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((594997567 / 500000000) : ℝ) ≤ Real.exp (2 * (44531 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44531 / 512000)) (594997567 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44547 / 512000) : ℝ)) ≤ (148758689 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44547 / 512000)) (148758689 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((74243588141 / 1000000) : ℝ) ≤ Real.exp (3 * (3738369 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3738369 / 1000000)) (74243588141 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44531 / 512000) : ℝ) (44547 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3738369 / 1000000) (3738723 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44531 / 512000) (44547 / 512000) (594997567 / 500000000) (148758689 / 125000000) (3738369 / 1000000) (3738723 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44531 / 512000) (44547 / 512000) (3738369 / 1000000) (3738723 / 1000000) (33469 / 1000) (16741 / 500)
    (10939 / 200) (549 / 10) (-5591 / 10) (361839 / 1000000) (1563087 / 500) (344811 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3738369 / 1000000) (74243588141 / 1000000) (344811 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3738369 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3738369 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell750 :
    ∀ t ∈ Set.Icc ((44547 / 512000) : ℝ) (44563 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1190069511 / 1000000000) : ℝ) ≤ Real.exp (2 * (44547 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44547 / 512000)) (1190069511 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44563 / 512000) : ℝ)) ≤ (595071947 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44563 / 512000)) (595071947 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2321741419 / 31250) : ℝ) ≤ Real.exp (3 * (3738603 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3738603 / 1000000)) (2321741419 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44547 / 512000) : ℝ) (44563 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3738603 / 1000000) (3738957 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44547 / 512000) (44563 / 512000) (1190069511 / 1000000000) (595071947 / 500000000) (3738603 / 1000000) (3738957 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44547 / 512000) (44563 / 512000) (3738603 / 1000000) (3738957 / 1000000) (16737 / 500) (4186 / 125)
    (2189 / 40) (54929 / 1000) (-69892 / 125) (361653 / 1000000) (3126957 / 1000) (344569 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3738603 / 1000000) (2321741419 / 31250) (344569 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3738603 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3738603 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell751 :
    ∀ t ∈ Set.Icc ((44563 / 512000) : ℝ) (44579 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1190143893 / 1000000000) : ℝ) ≤ Real.exp (2 * (44563 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44563 / 512000)) (1190143893 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44579 / 512000) : ℝ)) ≤ (29755457 / 25000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44579 / 512000)) (29755457 / 25000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((74347899289 / 1000000) : ℝ) ≤ Real.exp (3 * (3738837 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3738837 / 1000000)) (74347899289 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44563 / 512000) : ℝ) (44579 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3738837 / 1000000) (373919 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44563 / 512000) (44579 / 512000) (1190143893 / 1000000000) (29755457 / 25000000) (3738837 / 1000000) (373919 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44563 / 512000) (44579 / 512000) (3738837 / 1000000) (373919 / 100000) (837 / 25) (16747 / 500)
    (27377 / 500) (27479 / 500) (-559177 / 1000) (361467 / 1000000) (3127737 / 1000) (430409 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3738837 / 1000000) (74347899289 / 1000000) (430409 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3738837 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3738837 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell752 :
    ∀ t ∈ Set.Icc ((44579 / 512000) : ℝ) (8919 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1190218279 / 1000000000) : ℝ) ≤ Real.exp (2 * (44579 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44579 / 512000)) (1190218279 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8919 / 102400) : ℝ)) ≤ (1190292671 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8919 / 102400)) (1190292671 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4649992913 / 62500) : ℝ) ≤ Real.exp (3 * (373907 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (373907 / 100000)) (4649992913 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44579 / 512000) : ℝ) (8919 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (373907 / 100000) (116857 / 31250) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44579 / 512000) (8919 / 102400) (1190218279 / 1000000000) (1190292671 / 1000000000) (373907 / 100000) (116857 / 31250) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44579 / 512000) (8919 / 102400) (373907 / 100000) (116857 / 31250) (16743 / 500) (33499 / 1000)
    (6848 / 125) (13747 / 250) (-69901 / 125) (180641 / 500000) (78213 / 25) (1720433 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (373907 / 100000) (4649992913 / 62500) (1720433 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (373907 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (373907 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell753 :
    ∀ t ∈ Set.Icc ((8919 / 102400) : ℝ) (44611 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((119029267 / 100000000) : ℝ) ≤ Real.exp (2 * (8919 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8919 / 102400)) (119029267 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44611 / 512000) : ℝ)) ≤ (1190367067 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44611 / 512000)) (1190367067 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((14890426727 / 200000) : ℝ) ≤ Real.exp (3 * (467413 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (467413 / 125000)) (14890426727 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8919 / 102400) : ℝ) (44611 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (467413 / 125000) (1869829 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8919 / 102400) (44611 / 512000) (119029267 / 100000000) (1190367067 / 1000000000) (467413 / 125000) (1869829 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8919 / 102400) (44611 / 512000) (467413 / 125000) (1869829 / 500000) (33491 / 1000) (6701 / 200)
    (54813 / 1000) (27509 / 500) (-111849 / 200) (45137 / 125000) (3129303 / 1000) (3438451 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (467413 / 125000) (14890426727 / 200000) (3438451 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (467413 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (467413 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell754 :
    ∀ t ∈ Set.Icc ((44611 / 512000) : ℝ) (44627 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((595183533 / 500000000) : ℝ) ≤ Real.exp (2 * (44611 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44611 / 512000)) (595183533 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44627 / 512000) : ℝ)) ≤ (1190441467 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44627 / 512000)) (1190441467 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((9313052169 / 125000) : ℝ) ≤ Real.exp (3 * (1869769 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1869769 / 500000)) (9313052169 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44611 / 512000) : ℝ) (44627 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1869769 / 500000) (3739891 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44611 / 512000) (44627 / 512000) (595183533 / 500000000) (1190441467 / 1000000000) (1869769 / 500000) (3739891 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44611 / 512000) (44627 / 512000) (1869769 / 500000) (3739891 / 1000000) (33497 / 1000) (3351 / 100)
    (54843 / 1000) (55047 / 1000) (-111857 / 200) (36091 / 100000) (3130083 / 1000) (1718019 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1869769 / 500000) (9313052169 / 125000) (1718019 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1869769 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1869769 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell755 :
    ∀ t ∈ Set.Icc ((44627 / 512000) : ℝ) (44643 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((595220733 / 500000000) : ℝ) ≤ Real.exp (2 * (44627 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44627 / 512000)) (595220733 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44643 / 512000) : ℝ)) ≤ (37203621 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44643 / 512000)) (37203621 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((14911302823 / 200000) : ℝ) ≤ Real.exp (3 * (3739771 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3739771 / 1000000)) (14911302823 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44627 / 512000) : ℝ) (44643 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3739771 / 1000000) (29921 / 8000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44627 / 512000) (44643 / 512000) (595220733 / 500000000) (37203621 / 31250000) (3739771 / 1000000) (29921 / 8000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44627 / 512000) (44643 / 512000) (3739771 / 1000000) (29921 / 8000) (16751 / 500) (8379 / 250)
    (6859 / 125) (55077 / 1000) (-559317 / 1000) (180363 / 500000) (1565433 / 500) (3433637 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3739771 / 1000000) (14911302823 / 200000) (3433637 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3739771 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3739771 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell756 :
    ∀ t ∈ Set.Icc ((44643 / 512000) : ℝ) (44659 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1190515871 / 1000000000) : ℝ) ≤ Real.exp (2 * (44643 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44643 / 512000)) (1190515871 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44659 / 512000) : ℝ)) ≤ (595295141 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44659 / 512000)) (595295141 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((74608871133 / 1000000) : ℝ) ≤ Real.exp (3 * (748001 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (748001 / 200000)) (74608871133 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44643 / 512000) : ℝ) (44659 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (748001 / 200000) (3740359 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44643 / 512000) (44659 / 512000) (1190515871 / 1000000000) (595295141 / 500000000) (748001 / 200000) (3740359 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44643 / 512000) (44659 / 512000) (748001 / 200000) (3740359 / 1000000) (8377 / 250) (16761 / 500)
    (27451 / 500) (27553 / 500) (-559353 / 1000) (18027 / 50000) (62633 / 20) (857807 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (748001 / 200000) (74608871133 / 1000000) (857807 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (748001 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (748001 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell757 :
    ∀ t ∈ Set.Icc ((44659 / 512000) : ℝ) (1787 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1190590281 / 1000000000) : ℝ) ≤ Real.exp (2 * (44659 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44659 / 512000)) (1190590281 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1787 / 20480) : ℝ)) ≤ (148833087 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1787 / 20480)) (148833087 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((37330632459 / 500000) : ℝ) ≤ Real.exp (3 * (3740239 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3740239 / 1000000)) (37330632459 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44659 / 512000) : ℝ) (1787 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3740239 / 1000000) (3740593 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44659 / 512000) (1787 / 20480) (1190590281 / 1000000000) (148833087 / 125000000) (3740239 / 1000000) (3740593 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44659 / 512000) (1787 / 20480) (3740239 / 1000000) (3740593 / 1000000) (33513 / 1000) (33527 / 1000)
    (54931 / 1000) (6892 / 125) (-559389 / 1000) (72071 / 200000) (1566217 / 500) (171441 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3740239 / 1000000) (37330632459 / 500000) (171441 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3740239 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3740239 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell758 :
    ∀ t ∈ Set.Icc ((1787 / 20480) : ℝ) (44691 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((238132939 / 200000000) : ℝ) ≤ Real.exp (2 * (1787 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1787 / 20480)) (238132939 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44691 / 512000) : ℝ)) ≤ (238147823 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44691 / 512000)) (238147823 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((74713695497 / 1000000) : ℝ) ≤ Real.exp (3 * (3740473 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3740473 / 1000000)) (74713695497 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1787 / 20480) : ℝ) (44691 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3740473 / 1000000) (3740827 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1787 / 20480) (44691 / 512000) (238132939 / 200000000) (238147823 / 200000000) (3740473 / 1000000) (3740827 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1787 / 20480) (44691 / 512000) (3740473 / 1000000) (3740827 / 1000000) (33519 / 1000) (33533 / 1000)
    (54961 / 1000) (11033 / 200) (-22377 / 40) (36017 / 100000) (1566609 / 500) (1713207 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3740473 / 1000000) (74713695497 / 1000000) (1713207 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3740473 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3740473 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell759 :
    ∀ t ∈ Set.Icc ((44691 / 512000) : ℝ) (44707 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((595369557 / 500000000) : ℝ) ≤ Real.exp (2 * (44691 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44691 / 512000)) (595369557 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44707 / 512000) : ℝ)) ≤ (595406769 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44707 / 512000)) (595406769 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((74765938597 / 1000000) : ℝ) ≤ Real.exp (3 * (1870353 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1870353 / 500000)) (74765938597 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44691 / 512000) : ℝ) (44707 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1870353 / 500000) (187053 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44691 / 512000) (44707 / 512000) (595369557 / 500000000) (595406769 / 500000000) (1870353 / 500000) (187053 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44691 / 512000) (44707 / 512000) (1870353 / 500000) (187053 / 50000) (1341 / 40) (16769 / 500)
    (5499 / 100) (11039 / 200) (-27973 / 50) (71997 / 200000) (1566999 / 500) (171201 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1870353 / 500000) (74765938597 / 1000000) (171201 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1870353 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1870353 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch037 :
    ∀ t ∈ Set.Icc ((44387 / 512000) : ℝ) (44707 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell740
      hpThetaDensityLowerExpCompact_cell741)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell742
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell743
      hpThetaDensityLowerExpCompact_cell744)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell745
      hpThetaDensityLowerExpCompact_cell746)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell747
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell748
      hpThetaDensityLowerExpCompact_cell749))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell750
      hpThetaDensityLowerExpCompact_cell751)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell752
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell753
      hpThetaDensityLowerExpCompact_cell754)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell755
      hpThetaDensityLowerExpCompact_cell756)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell757
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell758
      hpThetaDensityLowerExpCompact_cell759)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch037
end HodgeProofHP
