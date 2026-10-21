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
theorem hpThetaDensityLowerExpCompact_cell1000 :
    ∀ t ∈ Set.Icc ((50707 / 512000) : ℝ) (162361 / 1638400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1219052867 / 1000000000) : ℝ) ≤ Real.exp (2 * (50707 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (50707 / 512000)) (1219052867 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((162361 / 1638400) : ℝ)) ≤ (1219199603 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (162361 / 1638400)) (1219199603 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4881604439 / 50000) : ℝ) ≤ Real.exp (3 * (1914827 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1914827 / 500000)) (4881604439 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((50707 / 512000) : ℝ) (162361 / 1638400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1914827 / 500000) (1915119 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (50707 / 512000) (162361 / 1638400) (1219052867 / 1000000000) (1219199603 / 1000000000) (1914827 / 500000) (1915119 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (50707 / 512000) (162361 / 1638400) (1914827 / 500000) (1915119 / 500000) (35683 / 1000) (7141 / 200)
    (8332 / 125) (13401 / 200) (-284963 / 500) (147931 / 500000) (1721841 / 500) (2622089 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1914827 / 500000) (4881604439 / 50000) (2622089 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1914827 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1914827 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell1001 :
    ∀ t ∈ Set.Icc ((162361 / 1638400) : ℝ) (519851 / 5242880), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((609599801 / 500000000) : ℝ) ≤ Real.exp (2 * (162361 / 1638400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (162361 / 1638400)) (609599801 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((519851 / 5242880) : ℝ)) ≤ (38104287 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (519851 / 5242880)) (38104287 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((97767207247 / 1000000) : ℝ) ≤ Real.exp (3 * (766023 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (766023 / 200000)) (97767207247 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((162361 / 1638400) : ℝ) (519851 / 5242880),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (766023 / 200000) (383067 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (162361 / 1638400) (519851 / 5242880) (609599801 / 500000000) (38104287 / 31250000) (766023 / 200000) (383067 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (162361 / 1638400) (519851 / 5242880) (766023 / 200000) (383067 / 100000) (7139 / 200) (8929 / 250)
    (33363 / 500) (33529 / 500) (-142529 / 250) (295553 / 1000000) (861309 / 250) (523693 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (766023 / 200000) (97767207247 / 1000000) (523693 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (766023 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (766023 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell1002 :
    ∀ t ∈ Set.Icc ((519851 / 5242880) : ℝ) (832649 / 8388608), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1219337183 / 1000000000) : ℝ) ≤ Real.exp (2 * (519851 / 5242880)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (519851 / 5242880)) (1219337183 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((832649 / 8388608) : ℝ)) ≤ (121959519 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (832649 / 8388608)) (121959519 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((24473498893 / 250000) : ℝ) ≤ Real.exp (3 * (3830547 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3830547 / 1000000)) (24473498893 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((519851 / 5242880) : ℝ) (832649 / 8388608),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3830547 / 1000000) (3831481 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (519851 / 5242880) (832649 / 8388608) (1219337183 / 1000000000) (121959519 / 100000000) (3830547 / 1000000) (3831481 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (519851 / 5242880) (832649 / 8388608) (3830547 / 1000000) (3831481 / 1000000) (35703 / 1000) (17869 / 500)
    (33349 / 500) (67257 / 1000) (-284159 / 500) (147679 / 500000) (689631 / 200) (1307537 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3830547 / 1000000) (24473498893 / 250000) (1307537 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3830547 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3830547 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell1003 :
    ∀ t ∈ Set.Icc ((832649 / 8388608) : ℝ) (33337019 / 335544320), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1219595189 / 1000000000) : ℝ) ≤ Real.exp (2 * (832649 / 8388608)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (832649 / 8388608)) (1219595189 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((33337019 / 335544320) : ℝ)) ≤ (1219820989 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (33337019 / 335544320)) (1219820989 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((49066230709 / 500000) : ℝ) ≤ Real.exp (3 * (1915679 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1915679 / 500000)) (49066230709 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((832649 / 8388608) : ℝ) (33337019 / 335544320),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1915679 / 500000) (383219 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (832649 / 8388608) (33337019 / 335544320) (1219595189 / 1000000000) (1219820989 / 1000000000) (1915679 / 500000) (383219 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (832649 / 8388608) (33337019 / 335544320) (1915679 / 500000) (383219 / 100000) (8931 / 250) (7151 / 200)
    (66833 / 1000) (67331 / 1000) (-284449 / 500) (73701 / 250000) (862677 / 250) (2608719 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1915679 / 500000) (49066230709 / 500000) (2608719 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1915679 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1915679 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell1004 :
    ∀ t ∈ Set.Icc ((33337019 / 335544320) : ℝ) (53382713 / 536870912), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((304955247 / 250000000) : ℝ) ≤ Real.exp (2 * (33337019 / 335544320)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (33337019 / 335544320)) (304955247 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((53382713 / 536870912) : ℝ)) ≤ (610009299 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (53382713 / 536870912)) (610009299 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((98341411109 / 1000000) : ℝ) ≤ Real.exp (3 * (3832067 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3832067 / 1000000)) (98341411109 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((33337019 / 335544320) : ℝ) (53382713 / 536870912),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3832067 / 1000000) (3832811 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (33337019 / 335544320) (53382713 / 536870912) (304955247 / 250000000) (610009299 / 500000000) (3832067 / 1000000) (3832811 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (33337019 / 335544320) (53382713 / 536870912) (3832067 / 1000000) (3832811 / 1000000) (17871 / 500) (3577 / 100)
    (1339 / 20) (16849 / 250) (-569399 / 1000) (3679 / 12500) (690589 / 200) (325397 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3832067 / 1000000) (98341411109 / 1000000) (325397 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3832067 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3832067 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell1005 :
    ∀ t ∈ Set.Icc ((53382713 / 536870912) : ℝ) (2136830411 / 21474836480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1220018597 / 1000000000) : ℝ) ≤ Real.exp (2 * (53382713 / 536870912)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (53382713 / 536870912)) (1220018597 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2136830411 / 21474836480) : ℝ)) ≤ (1220191533 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2136830411 / 21474836480)) (1220191533 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((12315598969 / 125000) : ℝ) ≤ Real.exp (3 * (239543 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (239543 / 62500)) (12315598969 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((53382713 / 536870912) : ℝ) (2136830411 / 21474836480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (239543 / 62500) (1916677 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (53382713 / 536870912) (2136830411 / 21474836480) (1220018597 / 1000000000) (1220191533 / 1000000000) (239543 / 62500) (1916677 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (53382713 / 536870912) (2136830411 / 21474836480) (239543 / 62500) (1916677 / 500000) (35757 / 1000) (35783 / 1000)
    (33527 / 500) (67453 / 1000) (-569843 / 1000) (293897 / 1000000) (1727451 / 500) (2598331 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (239543 / 62500) (12315598969 / 125000) (2598331 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (239543 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (239543 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell1006 :
    ∀ t ∈ Set.Icc ((2136830411 / 21474836480) : ℝ) (3421059305 / 34359738368), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((305047883 / 250000000) : ℝ) ≤ Real.exp (2 * (2136830411 / 21474836480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2136830411 / 21474836480)) (305047883 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3421059305 / 34359738368) : ℝ)) ≤ (122034287 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3421059305 / 34359738368)) (122034287 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((98685419283 / 1000000) : ℝ) ≤ Real.exp (3 * (3833231 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3833231 / 1000000)) (98685419283 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2136830411 / 21474836480) : ℝ) (3421059305 / 34359738368),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3833231 / 1000000) (383383 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2136830411 / 21474836480) (3421059305 / 34359738368) (305047883 / 250000000) (122034287 / 100000000) (3833231 / 1000000) (383383 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2136830411 / 21474836480) (3421059305 / 34359738368) (3833231 / 1000000) (383383 / 100000) (35771 / 1000) (17897 / 500)
    (8393 / 125) (67503 / 1000) (-285113 / 500) (36691 / 125000) (3456619 / 1000) (1297051 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3833231 / 1000000) (98685419283 / 1000000) (1297051 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3833231 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3833231 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell1007 :
    ∀ t ∈ Set.Icc ((3421059305 / 34359738368) : ℝ) (68495758759 / 687194767360), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1220342869 / 1000000000) : ℝ) ≤ Real.exp (2 * (3421059305 / 34359738368)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3421059305 / 34359738368)) (1220342869 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((68495758759 / 687194767360) : ℝ)) ≤ (305151939 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (68495758759 / 687194767360)) (305151939 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((24706610649 / 250000) : ℝ) ≤ Real.exp (3 * (3833707 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3833707 / 1000000)) (24706610649 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3421059305 / 34359738368) : ℝ) (68495758759 / 687194767360),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3833707 / 1000000) (1917331 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (3421059305 / 34359738368) (68495758759 / 687194767360) (1220342869 / 1000000000) (305151939 / 250000000) (3833707 / 1000000) (1917331 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (3421059305 / 34359738368) (68495758759 / 687194767360) (3833707 / 1000000) (1917331 / 500000) (35781 / 1000) (35817 / 1000)
    (8391 / 125) (677 / 10) (-568539 / 1000) (2933 / 10000) (172981 / 50) (1619 / 625000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3833707 / 1000000) (24706610649 / 250000) (1619 / 625000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3833707 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3833707 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell1008 :
    ∀ t ∈ Set.Icc ((68495758759 / 687194767360) : ℝ) (274206753013 / 2748779069440), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((244121551 / 200000000) : ℝ) ≤ Real.exp (2 * (68495758759 / 687194767360)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (68495758759 / 687194767360)) (244121551 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((274206753013 / 2748779069440) : ℝ)) ≤ (610403229 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (274206753013 / 2748779069440)) (610403229 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((49536710633 / 500000) : ℝ) ≤ Real.exp (3 * (3834539 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3834539 / 1000000)) (49536710633 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((68495758759 / 687194767360) : ℝ) (274206753013 / 2748779069440),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3834539 / 1000000) (1917643 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (68495758759 / 687194767360) (274206753013 / 2748779069440) (244121551 / 200000000) (610403229 / 500000000) (3834539 / 1000000) (1917643 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (68495758759 / 687194767360) (274206753013 / 2748779069440) (3834539 / 1000000) (1917643 / 500000) (35803 / 1000) (35831 / 1000)
    (6729 / 100) (33869 / 500) (-284819 / 500) (36589 / 125000) (432734 / 125) (2583943 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3834539 / 1000000) (49536710633 / 500000) (2583943 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3834539 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3834539 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell1009 :
    ∀ t ∈ Set.Icc ((274206753013 / 2748779069440) : ℝ) (1097498165983 / 10995116277760), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1220806457 / 1000000000) : ℝ) ≤ Real.exp (2 * (274206753013 / 2748779069440)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (274206753013 / 2748779069440)) (1220806457 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1097498165983 / 10995116277760) : ℝ)) ≤ (610477753 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1097498165983 / 10995116277760)) (610477753 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((99259060239 / 1000000) : ℝ) ≤ Real.exp (3 * (3835163 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3835163 / 1000000)) (99259060239 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((274206753013 / 2748779069440) : ℝ) (1097498165983 / 10995116277760),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3835163 / 1000000) (1917877 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (274206753013 / 2748779069440) (1097498165983 / 10995116277760) (1220806457 / 1000000000) (610477753 / 500000000) (3835163 / 1000000) (1917877 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (274206753013 / 2748779069440) (1097498165983 / 10995116277760) (3835163 / 1000000) (1917877 / 500000) (35819 / 1000) (17921 / 500)
    (16853 / 250) (33883 / 500) (-285231 / 500) (18267 / 62500) (3463563 / 1000) (257911 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3835163 / 1000000) (99259060239 / 1000000) (257911 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3835163 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3835163 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell1010 :
    ∀ t ∈ Set.Icc ((1097498165983 / 10995116277760) : ℝ) (2197009793759 / 21990232555520), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((244191101 / 200000000) : ℝ) ≤ Real.exp (2 * (1097498165983 / 10995116277760)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1097498165983 / 10995116277760)) (244191101 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2197009793759 / 21990232555520) : ℝ)) ≤ (152647389 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2197009793759 / 21990232555520)) (152647389 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((99398517703 / 1000000) : ℝ) ≤ Real.exp (3 * (3835631 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3835631 / 1000000)) (99398517703 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1097498165983 / 10995116277760) : ℝ) (2197009793759 / 21990232555520),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3835631 / 1000000) (3836457 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1097498165983 / 10995116277760) (2197009793759 / 21990232555520) (244191101 / 200000000) (152647389 / 125000000) (3835631 / 1000000) (3836457 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1097498165983 / 10995116277760) (2197009793759 / 21990232555520) (3835631 / 1000000) (3836457 / 1000000) (35829 / 1000) (1793 / 50)
    (33711 / 500) (33959 / 500) (-569363 / 1000) (146011 / 500000) (1733051 / 500) (643873 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3835631 / 1000000) (99398517703 / 1000000) (643873 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3835631 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3835631 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell1011 :
    ∀ t ∈ Set.Icc ((2197009793759 / 21990232555520) : ℝ) (1 / 10), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1221179111 / 1000000000) : ℝ) ≤ Real.exp (2 * (2197009793759 / 21990232555520)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2197009793759 / 21990232555520)) (1221179111 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1 / 10) : ℝ)) ≤ (1221402759 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1 / 10)) (1221402759 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((99608370189 / 1000000) : ℝ) ≤ Real.exp (3 * (1918167 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1918167 / 500000)) (99608370189 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2197009793759 / 21990232555520) : ℝ) (1 / 10),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1918167 / 500000) (3837159 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2197009793759 / 21990232555520) (1 / 10) (1221179111 / 1000000000) (1221402759 / 1000000000) (1918167 / 500000) (3837159 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2197009793759 / 21990232555520) (1 / 10) (1918167 / 500000) (3837159 / 1000000) (17923 / 500) (17939 / 500)
    (1688 / 25) (34007 / 500) (-569439 / 1000) (291567 / 1000000) (86716 / 25) (1285033 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1918167 / 500000) (99608370189 / 1000000) (1285033 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1918167 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1918167 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch050 :
    ∀ t ∈ Set.Icc ((50707 / 512000) : ℝ) (1 / 10),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell1000
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell1001
      hpThetaDensityLowerExpCompact_cell1002))
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell1003
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell1004
      hpThetaDensityLowerExpCompact_cell1005)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell1006
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell1007
      hpThetaDensityLowerExpCompact_cell1008))
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell1009
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell1010
      hpThetaDensityLowerExpCompact_cell1011))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch050
end HodgeProofHP
