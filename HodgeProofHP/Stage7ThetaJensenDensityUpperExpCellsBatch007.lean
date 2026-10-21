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
theorem hpThetaDensityUpperExpCompact_cell140 :
    ∀ t ∈ Set.Icc ((627 / 2000) : ℝ) (629 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((467996547 / 250000000) : ℝ) ≤ Real.exp (2 * (627 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (627 / 2000)) (467996547 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((629 / 2000) : ℝ)) ≤ (468933477 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (629 / 2000)) (468933477 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((45864178024133 / 1000000) : ℝ) ≤ Real.exp (3 * (1470211 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1470211 / 250000)) (45864178024133 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((627 / 2000) : ℝ) (629 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1470211 / 250000) (2946403 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (627 / 2000) (629 / 2000) (467996547 / 250000000) (468933477 / 250000000) (1470211 / 250000) (2946403 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (627 / 2000) (629 / 2000) (1470211 / 250000) (2946403 / 500000) (5149 / 50) (12952 / 125)
    (673537 / 1000) (171973 / 250) (505847 / 250) (1147 / 500000) (19293391 / 1000) (2791 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1470211 / 250000) (45864178024133 / 1000000) (2791 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1470211 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1470211 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell141 :
    ∀ t ∈ Set.Icc ((629 / 2000) : ℝ) (631 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1875733907 / 1000000000) : ℝ) ≤ Real.exp (2 * (629 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (629 / 2000)) (1875733907 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((631 / 2000) : ℝ)) ≤ (1879489129 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (631 / 2000)) (1879489129 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((23755579680667 / 500000) : ℝ) ≤ Real.exp (3 * (2946309 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2946309 / 500000)) (23755579680667 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((629 / 2000) : ℝ) (631 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2946309 / 500000) (1476151 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (629 / 2000) (631 / 2000) (1875733907 / 1000000000) (1879489129 / 1000000000) (2946309 / 500000) (1476151 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (629 / 2000) (631 / 2000) (2946309 / 500000) (1476151 / 250000) (12933 / 125) (52051 / 500)
    (679331 / 1000) (693763 / 1000) (412759 / 200) (557 / 250000) (3889673 / 200) (5389 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2946309 / 500000) (23755579680667 / 500000) (5389 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2946309 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2946309 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell142 :
    ∀ t ∈ Set.Icc ((631 / 2000) : ℝ) (633 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((234936141 / 125000000) : ℝ) ≤ Real.exp (2 * (631 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (631 / 2000)) (234936141 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((633 / 2000) : ℝ)) ≤ (1883251869 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (633 / 2000)) (1883251869 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((49220620145501 / 1000000) : ℝ) ≤ Real.exp (3 * (1180883 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1180883 / 200000)) (49220620145501 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((631 / 2000) : ℝ) (633 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1180883 / 200000) (236657 / 40000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (631 / 2000) (633 / 2000) (234936141 / 125000000) (1883251869 / 1000000000) (1180883 / 200000) (236657 / 40000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (631 / 2000) (633 / 2000) (1180883 / 200000) (236657 / 40000) (103949 / 1000) (10459 / 100)
    (342583 / 500) (174919 / 250) (2104709 / 1000) (541 / 250000) (2450572 / 125) (2601 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1180883 / 200000) (49220620145501 / 1000000) (2601 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1180883 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1180883 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell143 :
    ∀ t ∈ Set.Icc ((633 / 2000) : ℝ) (127 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((470812967 / 250000000) : ℝ) ≤ Real.exp (2 * (633 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (633 / 2000)) (470812967 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((127 / 400) : ℝ)) ≤ (943511071 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (127 / 400)) (943511071 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((50995042705289 / 1000000) : ℝ) ≤ Real.exp (3 * (1183247 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1183247 / 200000)) (50995042705289 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((633 / 2000) : ℝ) (127 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1183247 / 200000) (5928269 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (633 / 2000) (127 / 400) (470812967 / 250000000) (943511071 / 500000000) (1183247 / 200000) (5928269 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (633 / 2000) (127 / 400) (1183247 / 200000) (5928269 / 1000000) (104437 / 1000) (105081 / 1000)
    (138209 / 200) (88204 / 125) (2146137 / 1000) (2101 / 1000000) (2470254 / 125) (5021 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1183247 / 200000) (50995042705289 / 1000000) (5021 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1183247 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1183247 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell144 :
    ∀ t ∈ Set.Icc ((127 / 400) : ℝ) (637 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1887022141 / 1000000000) : ℝ) ≤ Real.exp (2 * (127 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (127 / 400)) (1887022141 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((637 / 2000) : ℝ)) ≤ (1890799963 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (637 / 2000)) (1890799963 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((10567465723441 / 200000) : ℝ) ≤ Real.exp (3 * (74101 / 12500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (74101 / 12500)) (10567465723441 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((127 / 400) : ℝ) (637 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (74101 / 12500) (2970069 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (127 / 400) (637 / 2000) (1887022141 / 1000000000) (1890799963 / 1000000000) (74101 / 12500) (2970069 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (127 / 400) (637 / 2000) (74101 / 12500) (2970069 / 500000) (104927 / 1000) (105573 / 1000)
    (348483 / 500) (88954 / 125) (218809 / 100) (51 / 25000) (1992077 / 100) (2423 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (74101 / 12500) (10567465723441 / 200000) (2423 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (74101 / 12500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (74101 / 12500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell145 :
    ∀ t ∈ Set.Icc ((637 / 2000) : ℝ) (639 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((945399981 / 500000000) : ℝ) ≤ Real.exp (2 * (637 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (637 / 2000)) (945399981 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((639 / 2000) : ℝ)) ≤ (1894585347 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (639 / 2000)) (1894585347 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((54749876160481 / 1000000) : ℝ) ≤ Real.exp (3 * (1484987 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1484987 / 250000)) (54749876160481 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((637 / 2000) : ℝ) (639 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1484987 / 250000) (595203 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (637 / 2000) (639 / 2000) (945399981 / 500000000) (1894585347 / 1000000000) (1484987 / 250000) (595203 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (637 / 2000) (639 / 2000) (1484987 / 250000) (595203 / 100000) (105419 / 1000) (106067 / 1000)
    (175733 / 250) (179419 / 250) (278821 / 125) (99 / 50000) (10040387 / 500) (1169 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1484987 / 250000) (54749876160481 / 1000000) (1169 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1484987 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1484987 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell146 :
    ∀ t ∈ Set.Icc ((639 / 2000) : ℝ) (641 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((947292673 / 500000000) : ℝ) ≤ Real.exp (2 * (639 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (639 / 2000)) (947292673 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((641 / 2000) : ℝ)) ≤ (1898378309 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (641 / 2000)) (1898378309 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((56735490258041 / 1000000) : ℝ) ≤ Real.exp (3 * (5951839 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5951839 / 1000000)) (56735490258041 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((639 / 2000) : ℝ) (641 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5951839 / 1000000) (2981973 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (639 / 2000) (641 / 2000) (947292673 / 500000000) (1898378309 / 1000000000) (5951839 / 1000000) (2981973 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (639 / 2000) (641 / 2000) (5951839 / 1000000) (2981973 / 500000) (105913 / 1000) (26641 / 250)
    (35447 / 50) (180941 / 250) (227359 / 100) (1923 / 1000000) (2530258 / 125) (4513 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5951839 / 1000000) (56735490258041 / 1000000) (4513 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5951839 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5951839 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell147 :
    ∀ t ∈ Set.Icc ((641 / 2000) : ℝ) (643 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((474594577 / 250000000) : ℝ) ≤ Real.exp (2 * (641 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (641 / 2000)) (474594577 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((643 / 2000) : ℝ)) ≤ (380435773 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (643 / 2000)) (380435773 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((58797444599241 / 1000000) : ℝ) ≤ Real.exp (3 * (1192751 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1192751 / 200000)) (58797444599241 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((641 / 2000) : ℝ) (643 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1192751 / 200000) (2987943 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (641 / 2000) (643 / 2000) (474594577 / 250000000) (380435773 / 200000000) (1192751 / 200000) (2987943 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (641 / 2000) (643 / 2000) (1192751 / 200000) (2987943 / 500000) (10641 / 100) (107063 / 1000)
    (714993 / 1000) (729897 / 1000) (2317139 / 1000) (933 / 500000) (20404653 / 1000) (2177 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1192751 / 200000) (58797444599241 / 1000000) (2177 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1192751 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1192751 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell148 :
    ∀ t ∈ Set.Icc ((643 / 2000) : ℝ) (129 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((118886179 / 62500000) : ℝ) ≤ Real.exp (2 * (643 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (643 / 2000)) (118886179 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((129 / 400) : ℝ)) ≤ (190598703 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (129 / 400)) (190598703 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((60938455407999 / 1000000) : ℝ) ≤ Real.exp (3 * (2987847 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2987847 / 500000)) (60938455407999 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((643 / 2000) : ℝ) (129 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2987847 / 500000) (5987849 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (643 / 2000) (129 / 400) (118886179 / 62500000) (190598703 / 100000000) (2987847 / 500000) (5987849 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (643 / 2000) (129 / 400) (2987847 / 500000) (5987849 / 1000000) (26727 / 250) (26891 / 250)
    (721089 / 1000) (736073 / 1000) (2361227 / 1000) (453 / 250000) (4113707 / 200) (4201 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2987847 / 500000) (60938455407999 / 1000000) (4201 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2987847 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2987847 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell149 :
    ∀ t ∈ Set.Icc ((129 / 400) : ℝ) (647 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1905987029 / 1000000000) : ℝ) ≤ Real.exp (2 * (129 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (129 / 400)) (1905987029 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((647 / 2000) : ℝ)) ≤ (954901409 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (647 / 2000)) (954901409 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63162072166377 / 1000000) : ℝ) ≤ Real.exp (3 * (2993829 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2993829 / 500000)) (63162072166377 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((129 / 400) : ℝ) (647 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2993829 / 500000) (5999837 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (129 / 400) (647 / 2000) (1905987029 / 1000000000) (954901409 / 500000000) (2993829 / 500000) (5999837 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (129 / 400) (647 / 2000) (2993829 / 500000) (5999837 / 1000000) (107409 / 1000) (108067 / 1000)
    (727231 / 1000) (92787 / 125) (2405869 / 1000) (1759 / 1000000) (20733747 / 1000) (2027 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2993829 / 500000) (63162072166377 / 1000000) (2027 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2993829 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2993829 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell150 :
    ∀ t ∈ Set.Icc ((647 / 2000) : ℝ) (649 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1909802817 / 1000000000) : ℝ) ≤ Real.exp (2 * (647 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (647 / 2000)) (1909802817 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((649 / 2000) : ℝ)) ≤ (956813123 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (649 / 2000)) (956813123 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32735623711069 / 500000) : ℝ) ≤ Real.exp (3 * (1199929 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1199929 / 200000)) (32735623711069 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((647 / 2000) : ℝ) (649 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1199929 / 200000) (6011849 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (647 / 2000) (649 / 2000) (1909802817 / 1000000000) (956813123 / 500000000) (1199929 / 200000) (6011849 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (647 / 2000) (649 / 2000) (1199929 / 200000) (6011849 / 1000000) (107911 / 1000) (27143 / 250)
    (366709 / 500) (187141 / 250) (1225539 / 500) (1707 / 1000000) (20900287 / 1000) (3911 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1199929 / 200000) (32735623711069 / 500000) (3911 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1199929 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1199929 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell151 :
    ∀ t ∈ Set.Icc ((649 / 2000) : ℝ) (651 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((382725249 / 200000000) : ℝ) ≤ Real.exp (2 * (649 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (649 / 2000)) (382725249 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((651 / 2000) : ℝ)) ≤ (119841083 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (651 / 2000)) (119841083 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((67869627340363 / 1000000) : ℝ) ≤ Real.exp (3 * (751457 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (751457 / 125000)) (67869627340363 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((649 / 2000) : ℝ) (651 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (751457 / 125000) (1505971 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (649 / 2000) (651 / 2000) (382725249 / 200000000) (119841083 / 62500000) (751457 / 125000) (1505971 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (649 / 2000) (651 / 2000) (751457 / 125000) (1505971 / 250000) (13552 / 125) (109079 / 1000)
    (739649 / 1000) (754877 / 1000) (312104 / 125) (207 / 125000) (421363 / 20) (943 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (751457 / 125000) (67869627340363 / 1000000) (943 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (751457 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (751457 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell152 :
    ∀ t ∈ Set.Icc ((651 / 2000) : ℝ) (653 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1917457327 / 1000000000) : ℝ) ≤ Real.exp (2 * (651 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (651 / 2000)) (1917457327 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((653 / 2000) : ℝ)) ≤ (1921296081 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (653 / 2000)) (1921296081 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3518051594997 / 50000) : ℝ) ≤ Real.exp (3 * (1505923 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1505923 / 250000)) (3518051594997 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((651 / 2000) : ℝ) (653 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1505923 / 250000) (754493 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (651 / 2000) (653 / 2000) (1917457327 / 1000000000) (1921296081 / 1000000000) (1505923 / 250000) (754493 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (651 / 2000) (653 / 2000) (1505923 / 250000) (754493 / 125000) (108923 / 1000) (109589 / 1000)
    (745927 / 1000) (190309 / 250) (635789 / 250) (1607 / 1000000) (21237373 / 1000) (3639 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1505923 / 250000) (3518051594997 / 50000) (3639 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1505923 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1505923 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell153 :
    ∀ t ∈ Set.Icc ((653 / 2000) : ℝ) (131 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((24016201 / 12500000) : ℝ) ≤ Real.exp (2 * (653 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (653 / 2000)) (24016201 / 12500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((131 / 400) : ℝ)) ≤ (962571259 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (131 / 400)) (962571259 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((72948808546117 / 1000000) : ℝ) ≤ Real.exp (3 * (6035751 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6035751 / 1000000)) (72948808546117 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((653 / 2000) : ℝ) (131 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6035751 / 1000000) (1512007 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (653 / 2000) (131 / 400) (24016201 / 12500000) (962571259 / 500000000) (6035751 / 1000000) (1512007 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (653 / 2000) (131 / 400) (6035751 / 1000000) (1512007 / 250000) (13679 / 125) (110101 / 1000)
    (3009 / 4) (767641 / 1000) (323758 / 125) (39 / 25000) (10703977 / 500) (351 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6035751 / 1000000) (72948808546117 / 1000000) (351 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6035751 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6035751 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell154 :
    ∀ t ∈ Set.Icc ((131 / 400) : ℝ) (657 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1925142517 / 1000000000) : ℝ) ≤ Real.exp (2 * (131 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (131 / 400)) (1925142517 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((657 / 2000) : ℝ)) ≤ (120562291 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (657 / 2000)) (120562291 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((75637306888117 / 1000000) : ℝ) ≤ Real.exp (3 * (1209567 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1209567 / 200000)) (75637306888117 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((131 / 400) : ℝ) (657 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1209567 / 200000) (757517 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (131 / 400) (657 / 2000) (1925142517 / 1000000000) (120562291 / 62500000) (1209567 / 200000) (757517 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (131 / 400) (657 / 2000) (1209567 / 200000) (757517 / 125000) (13743 / 125) (55307 / 500)
    (758619 / 1000) (774093 / 1000) (2637537 / 1000) (1513 / 1000000) (10789951 / 500) (677 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1209567 / 200000) (75637306888117 / 1000000) (677 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1209567 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1209567 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell155 :
    ∀ t ∈ Set.Icc ((657 / 2000) : ℝ) (659 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((385799331 / 200000000) : ℝ) ≤ Real.exp (2 * (657 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (657 / 2000)) (385799331 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((659 / 2000) : ℝ)) ≤ (193285851 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (659 / 2000)) (193285851 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15686033502829 / 200000) : ℝ) ≤ Real.exp (3 * (3029971 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3029971 / 500000)) (15686033502829 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((657 / 2000) : ℝ) (659 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3029971 / 500000) (6072269 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (657 / 2000) (659 / 2000) (385799331 / 200000000) (193285851 / 100000000) (3029971 / 500000) (6072269 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (657 / 2000) (659 / 2000) (3029971 / 500000) (6072269 / 1000000) (110457 / 1000) (111131 / 1000)
    (382517 / 500) (780593 / 1000) (2685623 / 1000) (367 / 250000) (21753243 / 1000) (653 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3029971 / 500000) (15686033502829 / 200000) (653 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3029971 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3029971 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell156 :
    ∀ t ∈ Set.Icc ((659 / 2000) : ℝ) (661 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1932858509 / 1000000000) : ℝ) ≤ Real.exp (2 * (659 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (659 / 2000)) (1932858509 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((661 / 2000) : ℝ)) ≤ (387345619 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (661 / 2000)) (387345619 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16266470816051 / 200000) : ℝ) ≤ Real.exp (3 * (242883 / 40000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (242883 / 40000)) (16266470816051 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((659 / 2000) : ℝ) (661 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (242883 / 40000) (243377 / 40000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (659 / 2000) (661 / 2000) (1932858509 / 1000000000) (387345619 / 200000000) (242883 / 40000) (243377 / 40000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (659 / 2000) (661 / 2000) (242883 / 40000) (243377 / 40000) (110973 / 1000) (111649 / 1000)
    (385749 / 500) (393569 / 500) (2734257 / 1000) (89 / 62500) (21927957 / 1000) (787 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (242883 / 40000) (16266470816051 / 200000) (787 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (242883 / 40000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (242883 / 40000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell157 :
    ∀ t ∈ Set.Icc ((661 / 2000) : ℝ) (663 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((968364047 / 500000000) : ℝ) ≤ Real.exp (2 * (661 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (661 / 2000)) (968364047 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((663 / 2000) : ℝ)) ≤ (1940605427 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (663 / 2000)) (1940605427 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2108690032129 / 25000) : ℝ) ≤ Real.exp (3 * (6084231 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6084231 / 1000000)) (2108690032129 / 25000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((661 / 2000) : ℝ) (663 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6084231 / 1000000) (6096607 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (661 / 2000) (663 / 2000) (968364047 / 500000000) (1940605427 / 1000000000) (6084231 / 1000000) (6096607 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (661 / 2000) (663 / 2000) (6084231 / 1000000) (6096607 / 1000000) (111491 / 1000) (11217 / 100)
    (389003 / 500) (793733 / 1000) (2783533 / 1000) (691 / 500000) (11052049 / 500) (759 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6084231 / 1000000) (2108690032129 / 25000) (759 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6084231 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6084231 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell158 :
    ∀ t ∈ Set.Icc ((663 / 2000) : ℝ) (133 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((970302713 / 500000000) : ℝ) ≤ Real.exp (2 * (663 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (663 / 2000)) (970302713 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((133 / 400) : ℝ)) ≤ (972245261 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (133 / 400)) (972245261 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((87480771611947 / 1000000) : ℝ) ≤ Real.exp (3 * (6096411 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6096411 / 1000000)) (87480771611947 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((663 / 2000) : ℝ) (133 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6096411 / 1000000) (1527203 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (663 / 2000) (133 / 400) (970302713 / 500000000) (972245261 / 500000000) (6096411 / 1000000) (1527203 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (663 / 2000) (133 / 400) (6096411 / 1000000) (1527203 / 250000) (28003 / 250) (28173 / 250)
    (784563 / 1000) (6403 / 8) (2833393 / 1000) (67 / 50000) (11140817 / 500) (2927 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6096411 / 1000000) (87480771611947 / 1000000) (2927 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6096411 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6096411 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell159 :
    ∀ t ∈ Set.Icc ((133 / 400) : ℝ) (667 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1944490521 / 1000000000) : ℝ) ≤ Real.exp (2 * (133 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (133 / 400)) (1944490521 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((667 / 2000) : ℝ)) ≤ (974191697 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (667 / 2000)) (974191697 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((90736960854741 / 1000000) : ℝ) ≤ Real.exp (3 * (763577 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (763577 / 125000)) (90736960854741 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((133 / 400) : ℝ) (667 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (763577 / 125000) (3060521 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (133 / 400) (667 / 2000) (1944490521 / 1000000000) (974191697 / 500000000) (763577 / 125000) (3060521 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (133 / 400) (667 / 2000) (763577 / 125000) (3060521 / 500000) (56267 / 500) (113217 / 1000)
    (791167 / 1000) (161413 / 200) (576773 / 200) (13 / 10000) (5615151 / 250) (1411 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (763577 / 125000) (90736960854741 / 1000000) (1411 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (763577 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (763577 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityUpperExpCompact_cellsBatch007 :
    ∀ t ∈ Set.Icc ((627 / 2000) : ℝ) (667 / 2000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell140
      hpThetaDensityUpperExpCompact_cell141)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell142
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell143
      hpThetaDensityUpperExpCompact_cell144)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell145
      hpThetaDensityUpperExpCompact_cell146)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell147
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell148
      hpThetaDensityUpperExpCompact_cell149))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell150
      hpThetaDensityUpperExpCompact_cell151)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell152
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell153
      hpThetaDensityUpperExpCompact_cell154)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell155
      hpThetaDensityUpperExpCompact_cell156)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell157
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell158
      hpThetaDensityUpperExpCompact_cell159)))))

#print axioms hpThetaDensityUpperExpCompact_cellsBatch007
end HodgeProofHP
