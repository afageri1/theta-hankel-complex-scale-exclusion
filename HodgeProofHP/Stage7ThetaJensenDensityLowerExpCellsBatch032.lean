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
theorem hpThetaDensityLowerExpCompact_cell640 :
    ∀ t ∈ Set.Icc ((43203 / 512000) : ℝ) (43211 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((591919009 / 500000000) : ℝ) ≤ Real.exp (2 * (43203 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43203 / 512000)) (591919009 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43211 / 512000) : ℝ)) ≤ (236775003 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43211 / 512000)) (236775003 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((35029069363 / 500000) : ℝ) ≤ Real.exp (3 * (3719027 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3719027 / 1000000)) (35029069363 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43203 / 512000) : ℝ) (43211 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3719027 / 1000000) (1859631 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43203 / 512000) (43211 / 512000) (591919009 / 500000000) (236775003 / 200000000) (3719027 / 1000000) (1859631 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43203 / 512000) (43211 / 512000) (3719027 / 1000000) (1859631 / 500000) (33009 / 1000) (16509 / 500)
    (10461 / 200) (1311 / 25) (-556551 / 1000) (377499 / 1000000) (3061591 / 1000) (913527 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3719027 / 1000000) (35029069363 / 500000) (913527 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3719027 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3719027 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell641 :
    ∀ t ∈ Set.Icc ((43211 / 512000) : ℝ) (43219 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((591937507 / 500000000) : ℝ) ≤ Real.exp (2 * (43211 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43211 / 512000)) (591937507 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43219 / 512000) : ℝ)) ≤ (295978003 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43219 / 512000)) (295978003 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((17520630797 / 250000) : ℝ) ≤ Real.exp (3 * (3719143 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3719143 / 1000000)) (17520630797 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43211 / 512000) : ℝ) (43219 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3719143 / 1000000) (1859689 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43211 / 512000) (43219 / 512000) (591937507 / 500000000) (295978003 / 250000000) (3719143 / 1000000) (1859689 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43211 / 512000) (43219 / 512000) (3719143 / 1000000) (1859689 / 500000) (33011 / 1000) (33021 / 1000)
    (1308 / 25) (10491 / 200) (-55657 / 100) (377403 / 1000000) (3061973 / 1000) (3652837 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3719143 / 1000000) (17520630797 / 250000) (3652837 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3719143 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3719143 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell642 :
    ∀ t ∈ Set.Icc ((43219 / 512000) : ℝ) (43227 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1183912011 / 1000000000) : ℝ) ≤ Real.exp (2 * (43219 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43219 / 512000)) (1183912011 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43227 / 512000) : ℝ)) ≤ (1183949009 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43227 / 512000)) (1183949009 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((35053458069 / 500000) : ℝ) ≤ Real.exp (3 * (3719259 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3719259 / 1000000)) (35053458069 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43219 / 512000) : ℝ) (43227 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3719259 / 1000000) (743899 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43219 / 512000) (43227 / 512000) (1183912011 / 1000000000) (1183949009 / 1000000000) (3719259 / 1000000) (743899 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43219 / 512000) (43227 / 512000) (3719259 / 1000000) (743899 / 200000) (16507 / 500) (4128 / 125)
    (26167 / 500) (52469 / 1000) (-69573 / 125) (377307 / 1000000) (1531179 / 500) (1825783 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3719259 / 1000000) (35053458069 / 500000) (1825783 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3719259 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3719259 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell643 :
    ∀ t ∈ Set.Icc ((43227 / 512000) : ℝ) (8647 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((73996813 / 62500000) : ℝ) ≤ Real.exp (2 * (43227 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43227 / 512000)) (73996813 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8647 / 102400) : ℝ)) ≤ (147998251 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8647 / 102400)) (147998251 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((35065658789 / 500000) : ℝ) ≤ Real.exp (3 * (5951 / 1600)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5951 / 1600)) (35065658789 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43227 / 512000) : ℝ) (8647 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5951 / 1600) (3719611 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43227 / 512000) (8647 / 102400) (73996813 / 62500000) (147998251 / 125000000) (5951 / 1600) (3719611 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43227 / 512000) (8647 / 102400) (5951 / 1600) (3719611 / 1000000) (33017 / 1000) (16513 / 500)
    (13087 / 250) (13121 / 250) (-556603 / 1000) (94303 / 250000) (153137 / 50) (456287 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5951 / 1600) (35065658789 / 500000) (456287 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5951 / 1600)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5951 / 1600)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell644 :
    ∀ t ∈ Set.Icc ((8647 / 102400) : ℝ) (43243 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1183986007 / 1000000000) : ℝ) ≤ Real.exp (2 * (8647 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8647 / 102400)) (1183986007 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43243 / 512000) : ℝ)) ≤ (1184023009 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43243 / 512000)) (1184023009 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((35077968989 / 500000) : ℝ) ≤ Real.exp (3 * (929873 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (929873 / 250000)) (35077968989 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8647 / 102400) : ℝ) (43243 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (929873 / 250000) (3719727 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8647 / 102400) (43243 / 512000) (1183986007 / 1000000000) (1184023009 / 1000000000) (929873 / 250000) (3719727 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8647 / 102400) (43243 / 512000) (929873 / 250000) (3719727 / 1000000) (1651 / 50) (33029 / 1000)
    (52363 / 1000) (26249 / 500) (-556627 / 1000) (188557 / 500000) (1531561 / 500) (729803 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (929873 / 250000) (35077968989 / 500000) (729803 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (929873 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (929873 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell645 :
    ∀ t ∈ Set.Icc ((43243 / 512000) : ℝ) (43251 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((37000719 / 31250000) : ℝ) ≤ Real.exp (2 * (43243 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43243 / 512000)) (37000719 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43251 / 512000) : ℝ)) ≤ (118406001 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43251 / 512000)) (118406001 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((219313614 / 3125) : ℝ) ≤ Real.exp (3 * (464951 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (464951 / 125000)) (219313614 / 3125) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43243 / 512000) : ℝ) (43251 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (464951 / 125000) (3719843 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43243 / 512000) (43251 / 512000) (37000719 / 31250000) (118406001 / 100000000) (464951 / 125000) (3719843 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43243 / 512000) (43251 / 512000) (464951 / 125000) (3719843 / 1000000) (16511 / 500) (4129 / 125)
    (52377 / 1000) (6564 / 125) (-278323 / 500) (188509 / 500000) (382938 / 125) (729549 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (464951 / 125000) (219313614 / 3125) (729549 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (464951 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (464951 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell646 :
    ∀ t ∈ Set.Icc ((43251 / 512000) : ℝ) (43259 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1184060009 / 1000000000) : ℝ) ≤ Real.exp (2 * (43251 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43251 / 512000)) (1184060009 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43259 / 512000) : ℝ)) ≤ (296024253 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43259 / 512000)) (296024253 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((35102391741 / 500000) : ℝ) ≤ Real.exp (3 * (929931 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (929931 / 250000)) (35102391741 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43251 / 512000) : ℝ) (43259 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (929931 / 250000) (92999 / 25000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43251 / 512000) (43259 / 512000) (1184060009 / 1000000000) (296024253 / 250000000) (929931 / 250000) (92999 / 25000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43251 / 512000) (43259 / 512000) (929931 / 250000) (92999 / 25000) (1321 / 40) (6607 / 200)
    (52391 / 1000) (52527 / 1000) (-556661 / 1000) (376923 / 1000000) (306389 / 100) (911619 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (929931 / 250000) (35102391741 / 500000) (911619 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (929931 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (929931 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell647 :
    ∀ t ∈ Set.Icc ((43259 / 512000) : ℝ) (43267 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1184097011 / 1000000000) : ℝ) ≤ Real.exp (2 * (43259 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43259 / 512000)) (1184097011 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43267 / 512000) : ℝ)) ≤ (9251047 / 7812500) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43267 / 512000)) (9251047 / 7812500) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((14045843797 / 200000) : ℝ) ≤ Real.exp (3 * (23249 / 6250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (23249 / 6250)) (14045843797 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43259 / 512000) : ℝ) (43267 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (23249 / 6250) (930019 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43259 / 512000) (43267 / 512000) (1184097011 / 1000000000) (9251047 / 7812500) (23249 / 6250) (930019 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43259 / 512000) (43267 / 512000) (23249 / 6250) (930019 / 250000) (8257 / 250) (33037 / 1000)
    (26203 / 500) (52541 / 1000) (-13917 / 25) (376827 / 1000000) (383034 / 125) (3645207 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (23249 / 6250) (14045843797 / 200000) (3645207 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (23249 / 6250)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (23249 / 6250)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell648 :
    ∀ t ∈ Set.Icc ((43267 / 512000) : ℝ) (1731 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((236826803 / 200000000) : ℝ) ≤ Real.exp (2 * (43267 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43267 / 512000)) (236826803 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1731 / 20480) : ℝ)) ≤ (1184171021 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1731 / 20480)) (1184171021 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((14050774751 / 200000) : ℝ) ≤ Real.exp (3 * (3719957 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3719957 / 1000000)) (14050774751 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43267 / 512000) : ℝ) (1731 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3719957 / 1000000) (58128 / 15625) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43267 / 512000) (1731 / 20480) (236826803 / 200000000) (1184171021 / 1000000000) (3719957 / 1000000) (58128 / 15625) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43267 / 512000) (1731 / 20480) (3719957 / 1000000) (58128 / 15625) (33031 / 1000) (826 / 25)
    (52421 / 1000) (13139 / 250) (-69588 / 125) (37673 / 100000) (1532327 / 500) (455491 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3719957 / 1000000) (14050774751 / 200000) (455491 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3719957 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3719957 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell649 :
    ∀ t ∈ Set.Icc ((1731 / 20480) : ℝ) (43283 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((59208551 / 50000000) : ℝ) ≤ Real.exp (2 * (1731 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1731 / 20480)) (59208551 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43283 / 512000) : ℝ)) ≤ (1184208027 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43283 / 512000)) (1184208027 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((14055665269 / 200000) : ℝ) ≤ Real.exp (3 * (3720073 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3720073 / 1000000)) (14055665269 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1731 / 20480) : ℝ) (43283 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3720073 / 1000000) (930077 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1731 / 20480) (43283 / 512000) (59208551 / 50000000) (1184208027 / 1000000000) (3720073 / 1000000) (930077 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1731 / 20480) (43283 / 512000) (3720073 / 1000000) (930077 / 250000) (33033 / 1000) (33043 / 1000)
    (10487 / 200) (5257 / 100) (-556723 / 1000) (188317 / 500000) (766259 / 250) (182133 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3720073 / 1000000) (14055665269 / 200000) (182133 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3720073 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3720073 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell650 :
    ∀ t ∈ Set.Icc ((43283 / 512000) : ℝ) (43291 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((592104013 / 500000000) : ℝ) ≤ Real.exp (2 * (43283 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43283 / 512000)) (592104013 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43291 / 512000) : ℝ)) ≤ (592122517 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43291 / 512000)) (592122517 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((35151393723 / 500000) : ℝ) ≤ Real.exp (3 * (3720189 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3720189 / 1000000)) (35151393723 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43283 / 512000) : ℝ) (43291 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3720189 / 1000000) (148817 / 40000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43283 / 512000) (43291 / 512000) (592104013 / 500000000) (592122517 / 500000000) (3720189 / 1000000) (148817 / 40000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43283 / 512000) (43291 / 512000) (3720189 / 1000000) (148817 / 40000) (8259 / 250) (16523 / 500)
    (52449 / 1000) (10517 / 200) (-556737 / 1000) (188269 / 500000) (1532711 / 500) (227587 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3720189 / 1000000) (35151393723 / 500000) (227587 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3720189 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3720189 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell651 :
    ∀ t ∈ Set.Icc ((43291 / 512000) : ℝ) (43299 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1184245033 / 1000000000) : ℝ) ≤ Real.exp (2 * (43291 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43291 / 512000)) (1184245033 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43299 / 512000) : ℝ)) ≤ (592141021 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43299 / 512000)) (592141021 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((70327257061 / 1000000) : ℝ) ≤ Real.exp (3 * (744061 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (744061 / 200000)) (70327257061 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43291 / 512000) : ℝ) (43299 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (744061 / 200000) (3720541 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43291 / 512000) (43299 / 512000) (1184245033 / 1000000000) (592141021 / 500000000) (744061 / 200000) (3720541 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43291 / 512000) (43299 / 512000) (744061 / 200000) (3720541 / 1000000) (33039 / 1000) (4131 / 125)
    (52463 / 1000) (52599 / 1000) (-139189 / 250) (376443 / 1000000) (766451 / 250) (29121 / 8000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (744061 / 200000) (70327257061 / 1000000) (29121 / 8000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (744061 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (744061 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell652 :
    ∀ t ∈ Set.Icc ((43299 / 512000) : ℝ) (43307 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1184282041 / 1000000000) : ℝ) ≤ Real.exp (2 * (43299 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43299 / 512000)) (1184282041 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43307 / 512000) : ℝ)) ≤ (1184319051 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43307 / 512000)) (1184319051 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8793993281 / 125000) : ℝ) ≤ Real.exp (3 * (1860211 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1860211 / 500000)) (8793993281 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43299 / 512000) : ℝ) (43307 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1860211 / 500000) (3720657 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43299 / 512000) (43307 / 512000) (1184282041 / 1000000000) (1184319051 / 1000000000) (1860211 / 500000) (3720657 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43299 / 512000) (43307 / 512000) (1860211 / 500000) (3720657 / 1000000) (16521 / 500) (33051 / 1000)
    (26239 / 500) (52613 / 1000) (-27839 / 50) (188173 / 500000) (3066187 / 1000) (56857 / 15625000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1860211 / 500000) (8793993281 / 125000) (56857 / 15625000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1860211 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1860211 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell653 :
    ∀ t ∈ Set.Icc ((43307 / 512000) : ℝ) (8663 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((23686381 / 20000000) : ℝ) ≤ Real.exp (2 * (43307 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43307 / 512000)) (23686381 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8663 / 102400) : ℝ)) ≤ (592178031 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8663 / 102400)) (592178031 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((70376432973 / 1000000) : ℝ) ≤ Real.exp (3 * (1860269 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1860269 / 500000)) (70376432973 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43307 / 512000) : ℝ) (8663 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1860269 / 500000) (1860387 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43307 / 512000) (8663 / 102400) (23686381 / 20000000) (592178031 / 500000000) (1860269 / 500000) (1860387 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43307 / 512000) (8663 / 102400) (1860269 / 500000) (1860387 / 500000) (8261 / 250) (16527 / 500)
    (13123 / 250) (13157 / 250) (-278397 / 500) (301 / 800) (766643 / 250) (1818791 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1860269 / 500000) (70376432973 / 1000000) (1818791 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1860269 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1860269 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell654 :
    ∀ t ∈ Set.Icc ((8663 / 102400) : ℝ) (43323 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1184356061 / 1000000000) : ℝ) ≤ Real.exp (2 * (8663 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8663 / 102400)) (1184356061 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43323 / 512000) : ℝ)) ≤ (592196537 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43323 / 512000)) (592196537 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3520046411 / 50000) : ℝ) ≤ Real.exp (3 * (1860327 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1860327 / 500000)) (3520046411 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8663 / 102400) : ℝ) (43323 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1860327 / 500000) (372089 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8663 / 102400) (43323 / 512000) (1184356061 / 1000000000) (592196537 / 500000000) (1860327 / 500000) (372089 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8663 / 102400) (43323 / 512000) (1860327 / 500000) (372089 / 100000) (33047 / 1000) (33057 / 1000)
    (52507 / 1000) (26321 / 500) (-556813 / 1000) (75231 / 200000) (613391 / 200) (909079 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1860327 / 500000) (3520046411 / 50000) (909079 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1860327 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1860327 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell655 :
    ∀ t ∈ Set.Icc ((43323 / 512000) : ℝ) (43331 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1184393073 / 1000000000) : ℝ) ≤ Real.exp (2 * (43323 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43323 / 512000)) (1184393073 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43331 / 512000) : ℝ)) ≤ (592215043 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43331 / 512000)) (592215043 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((35212715997 / 500000) : ℝ) ≤ Real.exp (3 * (372077 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (372077 / 100000)) (35212715997 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43323 / 512000) : ℝ) (43331 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (372077 / 100000) (1860503 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43323 / 512000) (43331 / 512000) (1184393073 / 1000000000) (592215043 / 500000000) (372077 / 100000) (1860503 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43323 / 512000) (43331 / 512000) (372077 / 100000) (1860503 / 500000) (661 / 20) (33059 / 1000)
    (52521 / 1000) (52657 / 1000) (-69604 / 125) (376059 / 1000000) (3067337 / 1000) (3635051 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (372077 / 100000) (35212715997 / 500000) (3635051 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (372077 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (372077 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell656 :
    ∀ t ∈ Set.Icc ((43331 / 512000) : ℝ) (43339 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((236886017 / 200000000) : ℝ) ≤ Real.exp (2 * (43331 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43331 / 512000)) (236886017 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43339 / 512000) : ℝ)) ≤ (11844671 / 10000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43339 / 512000)) (11844671 / 10000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((70450155647 / 1000000) : ℝ) ≤ Real.exp (3 * (3720887 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3720887 / 1000000)) (70450155647 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43331 / 512000) : ℝ) (43339 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3720887 / 1000000) (1860561 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43331 / 512000) (43339 / 512000) (236886017 / 200000000) (11844671 / 10000000) (3720887 / 1000000) (1860561 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43331 / 512000) (43339 / 512000) (3720887 / 1000000) (1860561 / 500000) (33053 / 1000) (16531 / 500)
    (6567 / 125) (52671 / 1000) (-69607 / 125) (187981 / 500000) (76693 / 25) (145351 / 40000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3720887 / 1000000) (70450155647 / 1000000) (145351 / 40000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3720887 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3720887 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell657 :
    ∀ t ∈ Set.Icc ((43339 / 512000) : ℝ) (43347 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1184467099 / 1000000000) : ℝ) ≤ Real.exp (2 * (43339 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43339 / 512000)) (1184467099 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43347 / 512000) : ℝ)) ≤ (296126029 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43347 / 512000)) (296126029 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((35237338277 / 500000) : ℝ) ≤ Real.exp (3 * (3721003 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3721003 / 1000000)) (35237338277 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43339 / 512000) : ℝ) (43347 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3721003 / 1000000) (3721239 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43339 / 512000) (43347 / 512000) (1184467099 / 1000000000) (296126029 / 250000000) (3721003 / 1000000) (3721239 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43339 / 512000) (43347 / 512000) (3721003 / 1000000) (3721239 / 1000000) (4132 / 125) (6613 / 200)
    (1051 / 20) (26343 / 500) (-556871 / 1000) (375867 / 1000000) (1534053 / 500) (3632511 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3721003 / 1000000) (35237338277 / 500000) (3632511 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3721003 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3721003 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell658 :
    ∀ t ∈ Set.Icc ((43347 / 512000) : ℝ) (8671 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((236900823 / 200000000) : ℝ) ≤ Real.exp (2 * (43347 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43347 / 512000)) (236900823 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8671 / 102400) : ℝ)) ≤ (296135283 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8671 / 102400)) (296135283 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((70499205997 / 1000000) : ℝ) ≤ Real.exp (3 * (3721119 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3721119 / 1000000)) (70499205997 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43347 / 512000) : ℝ) (8671 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3721119 / 1000000) (744271 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43347 / 512000) (8671 / 102400) (236900823 / 200000000) (296135283 / 250000000) (3721119 / 1000000) (744271 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43347 / 512000) (8671 / 102400) (3721119 / 1000000) (744271 / 200000) (16529 / 500) (8267 / 250)
    (13141 / 250) (527 / 10) (-55689 / 100) (375771 / 1000000) (383561 / 125) (3631247 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3721119 / 1000000) (70499205997 / 1000000) (3631247 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3721119 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3721119 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell659 :
    ∀ t ∈ Set.Icc ((8671 / 102400) : ℝ) (43363 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1184541131 / 1000000000) : ℝ) ≤ Real.exp (2 * (8671 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8671 / 102400)) (1184541131 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43363 / 512000) : ℝ)) ≤ (1184578149 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43363 / 512000)) (1184578149 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((70523743977 / 1000000) : ℝ) ≤ Real.exp (3 * (744247 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (744247 / 200000)) (70523743977 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8671 / 102400) : ℝ) (43363 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (744247 / 200000) (3721471 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8671 / 102400) (43363 / 512000) (1184541131 / 1000000000) (1184578149 / 1000000000) (744247 / 200000) (3721471 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8671 / 102400) (43363 / 512000) (744247 / 200000) (3721471 / 1000000) (33061 / 1000) (3307 / 100)
    (52579 / 1000) (26357 / 500) (-556909 / 1000) (93919 / 250000) (3068871 / 1000) (113437 / 31250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (744247 / 200000) (70523743977 / 1000000) (113437 / 31250000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (744247 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (744247 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch032 :
    ∀ t ∈ Set.Icc ((43203 / 512000) : ℝ) (43363 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell640
      hpThetaDensityLowerExpCompact_cell641)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell642
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell643
      hpThetaDensityLowerExpCompact_cell644)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell645
      hpThetaDensityLowerExpCompact_cell646)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell647
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell648
      hpThetaDensityLowerExpCompact_cell649))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell650
      hpThetaDensityLowerExpCompact_cell651)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell652
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell653
      hpThetaDensityLowerExpCompact_cell654)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell655
      hpThetaDensityLowerExpCompact_cell656)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell657
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell658
      hpThetaDensityLowerExpCompact_cell659)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch032
end HodgeProofHP
