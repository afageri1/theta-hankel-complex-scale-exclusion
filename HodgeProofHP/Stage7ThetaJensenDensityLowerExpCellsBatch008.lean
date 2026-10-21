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
theorem hpThetaDensityLowerExpCompact_cell160 :
    ∀ t ∈ Set.Icc ((41129 / 512000) : ℝ) (41131 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174285827 / 1000000000) : ℝ) ≤ Real.exp (2 * (41129 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41129 / 512000)) (1174285827 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41131 / 512000) : ℝ)) ≤ (587147501 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41131 / 512000)) (587147501 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2000830993 / 31250) : ℝ) ≤ Real.exp (3 * (1844509 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1844509 / 500000)) (2000830993 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41129 / 512000) : ℝ) (41131 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1844509 / 500000) (1844583 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41129 / 512000) (41131 / 512000) (1174285827 / 1000000000) (587147501 / 500000000) (1844509 / 500000) (1844583 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41129 / 512000) (41131 / 512000) (1844509 / 500000) (1844583 / 500000) (323 / 10) (16153 / 500)
    (48663 / 1000) (48747 / 1000) (-551777 / 1000) (80623 / 200000) (296369 / 100) (3998339 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1844509 / 500000) (2000830993 / 31250) (3998339 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844509 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844509 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell161 :
    ∀ t ∈ Set.Icc ((41131 / 512000) : ℝ) (41133 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174295001 / 1000000000) : ℝ) ≤ Real.exp (2 * (41131 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41131 / 512000)) (1174295001 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41133 / 512000) : ℝ)) ≤ (73394011 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41133 / 512000)) (73394011 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64032162329 / 1000000) : ℝ) ≤ Real.exp (3 * (3689047 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3689047 / 1000000)) (64032162329 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41131 / 512000) : ℝ) (41133 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3689047 / 1000000) (1844597 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41131 / 512000) (41133 / 512000) (1174295001 / 1000000000) (73394011 / 62500000) (3689047 / 1000000) (1844597 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41131 / 512000) (41133 / 512000) (3689047 / 1000000) (1844597 / 500000) (32301 / 1000) (32307 / 1000)
    (48667 / 1000) (195 / 4) (-551787 / 1000) (403089 / 1000000) (148189 / 50) (3997991 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3689047 / 1000000) (64032162329 / 1000000) (3997991 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689047 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689047 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell162 :
    ∀ t ∈ Set.Icc ((41133 / 512000) : ℝ) (20567 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((46972167 / 40000000) : ℝ) ≤ Real.exp (2 * (41133 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41133 / 512000)) (46972167 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20567 / 256000) : ℝ)) ≤ (1174308763 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20567 / 256000)) (1174308763 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64037733367 / 1000000) : ℝ) ≤ Real.exp (3 * (922269 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (922269 / 250000)) (64037733367 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41133 / 512000) : ℝ) (20567 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (922269 / 250000) (3689209 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41133 / 512000) (20567 / 256000) (46972167 / 40000000) (1174308763 / 1000000000) (922269 / 250000) (3689209 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41133 / 512000) (20567 / 256000) (922269 / 250000) (3689209 / 1000000) (32301 / 1000) (32307 / 1000)
    (48673 / 1000) (48749 / 1000) (-275927 / 500) (403059 / 1000000) (2963829 / 1000) (999411 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (922269 / 250000) (64037733367 / 1000000) (999411 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922269 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922269 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell163 :
    ∀ t ∈ Set.Icc ((20567 / 256000) : ℝ) (2571 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587154381 / 500000000) : ℝ) ≤ Real.exp (2 * (20567 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20567 / 256000)) (587154381 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2571 / 32000) : ℝ)) ≤ (587158969 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2571 / 32000)) (587158969 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64040423007 / 1000000) : ℝ) ≤ Real.exp (3 * (368909 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (368909 / 100000)) (64040423007 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20567 / 256000) : ℝ) (2571 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (368909 / 100000) (1844619 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20567 / 256000) (2571 / 32000) (587154381 / 500000000) (587158969 / 500000000) (368909 / 100000) (1844619 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20567 / 256000) (2571 / 32000) (368909 / 100000) (1844619 / 500000) (16151 / 500) (8077 / 250)
    (6084 / 125) (12189 / 250) (-55179 / 100) (403051 / 1000000) (1481961 / 500) (999369 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (368909 / 100000) (64040423007 / 1000000) (999369 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (368909 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (368909 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell164 :
    ∀ t ∈ Set.Icc ((2571 / 32000) : ℝ) (41137 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174317937 / 1000000000) : ℝ) ≤ Real.exp (2 * (2571 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2571 / 32000)) (1174317937 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41137 / 512000) : ℝ)) ≤ (46972901 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41137 / 512000)) (46972901 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16011498691 / 250000) : ℝ) ≤ Real.exp (3 * (3689119 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3689119 / 1000000)) (16011498691 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2571 / 32000) : ℝ) (41137 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3689119 / 1000000) (922313 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2571 / 32000) (41137 / 512000) (1174317937 / 1000000000) (46972901 / 40000000) (3689119 / 1000000) (922313 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2571 / 32000) (41137 / 512000) (3689119 / 1000000) (922313 / 250000) (16151 / 500) (8077 / 250)
    (24339 / 500) (24377 / 500) (-275931 / 500) (403021 / 1000000) (2963967 / 1000) (499641 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3689119 / 1000000) (16011498691 / 250000) (499641 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689119 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689119 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell165 :
    ∀ t ∈ Set.Icc ((41137 / 512000) : ℝ) (41139 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293580631 / 250000000) : ℝ) ≤ Real.exp (2 * (41137 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41137 / 512000)) (293580631 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41139 / 512000) : ℝ)) ≤ (1174331699 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41139 / 512000)) (1174331699 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32024438449 / 500000) : ℝ) ≤ Real.exp (3 * (1844567 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1844567 / 500000)) (32024438449 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41137 / 512000) : ℝ) (41139 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1844567 / 500000) (3689281 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41137 / 512000) (41139 / 512000) (293580631 / 250000000) (1174331699 / 1000000000) (1844567 / 500000) (3689281 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41137 / 512000) (41139 / 512000) (1844567 / 500000) (3689281 / 1000000) (32303 / 1000) (32309 / 1000)
    (48677 / 1000) (48761 / 1000) (-275901 / 500) (100753 / 250000) (148203 / 50) (999237 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1844567 / 500000) (32024438449 / 500000) (999237 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844567 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844567 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell166 :
    ∀ t ∈ Set.Icc ((41139 / 512000) : ℝ) (41141 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587165849 / 500000000) : ℝ) ≤ Real.exp (2 * (41139 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41139 / 512000)) (587165849 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41141 / 512000) : ℝ)) ≤ (587170437 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41141 / 512000)) (587170437 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6405444939 / 100000) : ℝ) ≤ Real.exp (3 * (3689163 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3689163 / 1000000)) (6405444939 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41139 / 512000) : ℝ) (41141 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3689163 / 1000000) (368931 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41139 / 512000) (41141 / 512000) (587165849 / 500000000) (587170437 / 500000000) (3689163 / 1000000) (368931 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41139 / 512000) (41141 / 512000) (3689163 / 1000000) (368931 / 100000) (32303 / 1000) (3231 / 100)
    (48681 / 1000) (12191 / 250) (-551807 / 1000) (201493 / 500000) (2964153 / 1000) (19983 / 5000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3689163 / 1000000) (6405444939 / 100000) (19983 / 5000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689163 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689163 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell167 :
    ∀ t ∈ Set.Icc ((41141 / 512000) : ℝ) (41143 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174340873 / 1000000000) : ℝ) ≤ Real.exp (2 * (41141 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41141 / 512000)) (1174340873 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41143 / 512000) : ℝ)) ≤ (36698439 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41143 / 512000)) (36698439 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64059830187 / 1000000) : ℝ) ≤ Real.exp (3 * (3689191 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3689191 / 1000000)) (64059830187 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41141 / 512000) : ℝ) (41143 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3689191 / 1000000) (3689339 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41141 / 512000) (41143 / 512000) (1174340873 / 1000000000) (36698439 / 31250000) (3689191 / 1000000) (3689339 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41141 / 512000) (41143 / 512000) (3689191 / 1000000) (3689339 / 1000000) (4038 / 125) (3231 / 100)
    (12171 / 250) (6096 / 125) (-68976 / 125) (201481 / 500000) (1482123 / 500) (799253 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3689191 / 1000000) (64059830187 / 1000000) (799253 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689191 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689191 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell168 :
    ∀ t ∈ Set.Icc ((41143 / 512000) : ℝ) (8229 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174350047 / 1000000000) : ℝ) ≤ Real.exp (2 * (41143 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41143 / 512000)) (1174350047 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8229 / 102400) : ℝ)) ≤ (1174359223 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8229 / 102400)) (1174359223 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4004087727 / 62500) : ℝ) ≤ Real.exp (3 * (184461 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (184461 / 50000)) (4004087727 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41143 / 512000) : ℝ) (8229 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (184461 / 50000) (3689367 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41143 / 512000) (8229 / 102400) (1174350047 / 1000000000) (1174359223 / 1000000000) (184461 / 50000) (3689367 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41143 / 512000) (8229 / 102400) (184461 / 50000) (3689367 / 1000000) (6461 / 200) (32311 / 1000)
    (48687 / 1000) (48771 / 1000) (-275909 / 500) (50367 / 125000) (370542 / 125) (3995917 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (184461 / 50000) (4004087727 / 62500) (3995917 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (184461 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (184461 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell169 :
    ∀ t ∈ Set.Icc ((8229 / 102400) : ℝ) (41147 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587179611 / 500000000) : ℝ) ≤ Real.exp (2 * (8229 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8229 / 102400)) (587179611 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41147 / 512000) : ℝ)) ≤ (587184199 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41147 / 512000)) (587184199 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32035488781 / 500000) : ℝ) ≤ Real.exp (3 * (3689249 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3689249 / 1000000)) (32035488781 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8229 / 102400) : ℝ) (41147 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3689249 / 1000000) (922349 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8229 / 102400) (41147 / 512000) (587179611 / 500000000) (587184199 / 500000000) (3689249 / 1000000) (922349 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8229 / 102400) (41147 / 512000) (3689249 / 1000000) (922349 / 250000) (6461 / 200) (4039 / 125)
    (48691 / 1000) (1951 / 40) (-551823 / 1000) (402911 / 1000000) (296443 / 100) (3995569 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3689249 / 1000000) (32035488781 / 500000) (3995569 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689249 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689249 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell170 :
    ∀ t ∈ Set.Icc ((41147 / 512000) : ℝ) (41149 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174368397 / 1000000000) : ℝ) ≤ Real.exp (2 * (41147 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41147 / 512000)) (1174368397 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41149 / 512000) : ℝ)) ≤ (293594393 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41149 / 512000)) (293594393 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32038275989 / 500000) : ℝ) ≤ Real.exp (3 * (1844639 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1844639 / 500000)) (32038275989 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41147 / 512000) : ℝ) (41149 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1844639 / 500000) (147577 / 40000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41147 / 512000) (41149 / 512000) (1174368397 / 1000000000) (293594393 / 250000000) (1844639 / 500000) (147577 / 40000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41147 / 512000) (41149 / 512000) (1844639 / 500000) (147577 / 40000) (16153 / 500) (4039 / 125)
    (24347 / 500) (24389 / 500) (-137957 / 250) (80577 / 200000) (2964523 / 1000) (1997611 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1844639 / 500000) (32038275989 / 500000) (1997611 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844639 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844639 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell171 :
    ∀ t ∈ Set.Icc ((41149 / 512000) : ℝ) (41151 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174377571 / 1000000000) : ℝ) ≤ Real.exp (2 * (41149 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41149 / 512000)) (1174377571 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41151 / 512000) : ℝ)) ≤ (1174386747 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41151 / 512000)) (1174386747 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32041063439 / 500000) : ℝ) ≤ Real.exp (3 * (3689307 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3689307 / 1000000)) (32041063439 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41149 / 512000) : ℝ) (41151 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3689307 / 1000000) (1844727 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41149 / 512000) (41151 / 512000) (1174377571 / 1000000000) (1174386747 / 1000000000) (3689307 / 1000000) (1844727 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41149 / 512000) (41151 / 512000) (3689307 / 1000000) (1844727 / 500000) (32307 / 1000) (32313 / 1000)
    (24349 / 500) (24391 / 500) (-551833 / 1000) (20143 / 50000) (370577 / 125) (1997437 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3689307 / 1000000) (32041063439 / 500000) (1997437 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689307 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689307 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell172 :
    ∀ t ∈ Set.Icc ((41151 / 512000) : ℝ) (41153 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587193373 / 500000000) : ℝ) ≤ Real.exp (2 * (41151 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41151 / 512000)) (587193373 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41153 / 512000) : ℝ)) ≤ (587197961 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41153 / 512000)) (587197961 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6408751 / 100) : ℝ) ≤ Real.exp (3 * (737867 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (737867 / 200000)) (6408751 / 100) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41151 / 512000) : ℝ) (41153 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (737867 / 200000) (3689483 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41151 / 512000) (41153 / 512000) (587193373 / 500000000) (587197961 / 500000000) (737867 / 200000) (3689483 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41151 / 512000) (41153 / 512000) (737867 / 200000) (3689483 / 1000000) (32307 / 1000) (16157 / 500)
    (48701 / 1000) (9757 / 200) (-275917 / 500) (80567 / 200000) (2964709 / 1000) (3994539 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (737867 / 200000) (6408751 / 100) (3994539 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (737867 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (737867 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell173 :
    ∀ t ∈ Set.Icc ((41153 / 512000) : ℝ) (8231 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174395921 / 1000000000) : ℝ) ≤ Real.exp (2 * (41153 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41153 / 512000)) (1174395921 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8231 / 102400) : ℝ)) ≤ (1174405097 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8231 / 102400)) (1174405097 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64093085853 / 1000000) : ℝ) ≤ Real.exp (3 * (922341 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (922341 / 250000)) (64093085853 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41153 / 512000) : ℝ) (8231 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (922341 / 250000) (461189 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41153 / 512000) (8231 / 102400) (1174395921 / 1000000000) (1174405097 / 1000000000) (922341 / 250000) (461189 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41153 / 512000) (8231 / 102400) (922341 / 250000) (461189 / 125000) (8077 / 250) (16157 / 500)
    (6088 / 125) (48789 / 1000) (-551839 / 1000) (40281 / 100000) (1482401 / 500) (3994191 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (922341 / 250000) (64093085853 / 1000000) (3994191 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922341 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922341 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell174 :
    ∀ t ∈ Set.Icc ((8231 / 102400) : ℝ) (41157 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((146800637 / 125000000) : ℝ) ≤ Real.exp (2 * (8231 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8231 / 102400)) (146800637 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41157 / 512000) : ℝ)) ≤ (18350223 / 15625000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41157 / 512000)) (18350223 / 15625000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4006166387 / 62500) : ℝ) ≤ Real.exp (3 * (3689393 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3689393 / 1000000)) (4006166387 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8231 / 102400) : ℝ) (41157 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3689393 / 1000000) (184477 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8231 / 102400) (41157 / 512000) (146800637 / 125000000) (18350223 / 15625000) (3689393 / 1000000) (184477 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8231 / 102400) (41157 / 512000) (3689393 / 1000000) (184477 / 50000) (32309 / 1000) (6463 / 200)
    (12177 / 250) (6099 / 125) (-551849 / 1000) (12587 / 31250) (741223 / 250) (998461 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3689393 / 1000000) (4006166387 / 62500) (998461 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689393 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689393 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell175 :
    ∀ t ∈ Set.Icc ((41157 / 512000) : ℝ) (41159 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174414271 / 1000000000) : ℝ) ≤ Real.exp (2 * (41157 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41157 / 512000)) (1174414271 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41159 / 512000) : ℝ)) ≤ (1174423447 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41159 / 512000)) (1174423447 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8013029877 / 125000) : ℝ) ≤ Real.exp (3 * (1844711 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1844711 / 500000)) (8013029877 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41157 / 512000) : ℝ) (41159 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1844711 / 500000) (3689569 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41157 / 512000) (41159 / 512000) (1174414271 / 1000000000) (1174423447 / 1000000000) (1844711 / 500000) (3689569 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41157 / 512000) (41159 / 512000) (1844711 / 500000) (3689569 / 1000000) (32309 / 1000) (8079 / 250)
    (6089 / 125) (9759 / 200) (-275927 / 500) (201379 / 500000) (1482493 / 500) (499187 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1844711 / 500000) (8013029877 / 125000) (499187 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844711 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844711 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell176 :
    ∀ t ∈ Set.Icc ((41159 / 512000) : ℝ) (41161 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587211723 / 500000000) : ℝ) ≤ Real.exp (2 * (41159 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41159 / 512000)) (587211723 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41161 / 512000) : ℝ)) ≤ (1174432623 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41161 / 512000)) (1174432623 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2564392653 / 40000) : ℝ) ≤ Real.exp (3 * (3689451 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3689451 / 1000000)) (2564392653 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41159 / 512000) : ℝ) (41161 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3689451 / 1000000) (1844799 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41159 / 512000) (41161 / 512000) (587211723 / 500000000) (1174432623 / 1000000000) (3689451 / 1000000) (1844799 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41159 / 512000) (41161 / 512000) (3689451 / 1000000) (1844799 / 500000) (3231 / 100) (8079 / 250)
    (9743 / 200) (48799 / 1000) (-551859 / 1000) (402733 / 1000000) (2965079 / 1000) (3993149 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3689451 / 1000000) (2564392653 / 40000) (3993149 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689451 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689451 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell177 :
    ∀ t ∈ Set.Icc ((41161 / 512000) : ℝ) (41163 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587216311 / 500000000) : ℝ) ≤ Real.exp (2 * (41161 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41161 / 512000)) (587216311 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41163 / 512000) : ℝ)) ≤ (587220899 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41163 / 512000)) (587220899 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64115394119 / 1000000) : ℝ) ≤ Real.exp (3 * (92237 / 25000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (92237 / 25000)) (64115394119 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41161 / 512000) : ℝ) (41163 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (92237 / 25000) (3689627 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41161 / 512000) (41163 / 512000) (587216311 / 500000000) (587220899 / 500000000) (92237 / 25000) (3689627 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41161 / 512000) (41163 / 512000) (92237 / 25000) (3689627 / 1000000) (32311 / 1000) (32317 / 1000)
    (48719 / 1000) (24401 / 500) (-68983 / 125) (402707 / 1000000) (741293 / 250) (3992801 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (92237 / 25000) (64115394119 / 1000000) (3992801 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (92237 / 25000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (92237 / 25000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell178 :
    ∀ t ∈ Set.Icc ((41163 / 512000) : ℝ) (8233 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174441797 / 1000000000) : ℝ) ≤ Real.exp (2 * (41163 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41163 / 512000)) (1174441797 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8233 / 102400) : ℝ)) ≤ (1174450973 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8233 / 102400)) (1174450973 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16030195009 / 250000) : ℝ) ≤ Real.exp (3 * (922377 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (922377 / 250000)) (16030195009 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41163 / 512000) : ℝ) (8233 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (922377 / 250000) (461207 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41163 / 512000) (8233 / 102400) (1174441797 / 1000000000) (1174450973 / 1000000000) (922377 / 250000) (461207 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41163 / 512000) (8233 / 102400) (922377 / 250000) (461207 / 125000) (32311 / 1000) (16159 / 500)
    (24361 / 500) (24403 / 500) (-110373 / 200) (402683 / 1000000) (593053 / 200) (1996233 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (922377 / 250000) (16030195009 / 250000) (1996233 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922377 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922377 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell179 :
    ∀ t ∈ Set.Icc ((8233 / 102400) : ℝ) (41167 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293612743 / 250000000) : ℝ) ≤ Real.exp (2 * (8233 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8233 / 102400)) (293612743 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41167 / 512000) : ℝ)) ≤ (1174460149 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41167 / 512000)) (1174460149 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1001974356 / 15625) : ℝ) ≤ Real.exp (3 * (3689537 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3689537 / 1000000)) (1001974356 / 15625) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8233 / 102400) : ℝ) (41167 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3689537 / 1000000) (737937 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8233 / 102400) (41167 / 512000) (293612743 / 250000000) (1174460149 / 1000000000) (3689537 / 1000000) (737937 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8233 / 102400) (41167 / 512000) (3689537 / 1000000) (737937 / 200000) (4039 / 125) (16159 / 500)
    (1949 / 40) (4881 / 100) (-55187 / 100) (402657 / 1000000) (2965359 / 1000) (3992119 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3689537 / 1000000) (1001974356 / 15625) (3992119 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689537 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689537 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch008 :
    ∀ t ∈ Set.Icc ((41129 / 512000) : ℝ) (41167 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell160
      hpThetaDensityLowerExpCompact_cell161)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell162
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell163
      hpThetaDensityLowerExpCompact_cell164)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell165
      hpThetaDensityLowerExpCompact_cell166)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell167
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell168
      hpThetaDensityLowerExpCompact_cell169))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell170
      hpThetaDensityLowerExpCompact_cell171)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell172
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell173
      hpThetaDensityLowerExpCompact_cell174)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell175
      hpThetaDensityLowerExpCompact_cell176)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell177
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell178
      hpThetaDensityLowerExpCompact_cell179)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch008
end HodgeProofHP
