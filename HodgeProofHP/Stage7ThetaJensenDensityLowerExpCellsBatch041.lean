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
theorem hpThetaDensityLowerExpCompact_cell820 :
    ∀ t ∈ Set.Icc ((45667 / 512000) : ℝ) (45683 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1195287471 / 1000000000) : ℝ) ≤ Real.exp (2 * (45667 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45667 / 512000)) (1195287471 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45683 / 512000) : ℝ)) ≤ (59768109 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45683 / 512000)) (59768109 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((78040614437 / 1000000) : ℝ) ≤ Real.exp (3 * (750999 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (750999 / 200000)) (78040614437 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45667 / 512000) : ℝ) (45683 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (750999 / 200000) (75107 / 20000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45667 / 512000) (45683 / 512000) (1195287471 / 1000000000) (59768109 / 50000000) (750999 / 200000) (75107 / 20000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45667 / 512000) (45683 / 512000) (750999 / 200000) (75107 / 20000) (33867 / 1000) (33881 / 1000)
    (7101 / 125) (28507 / 500) (-561599 / 1000) (348847 / 1000000) (1591079 / 500) (410043 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (750999 / 200000) (78040614437 / 1000000) (410043 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (750999 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (750999 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell821 :
    ∀ t ∈ Set.Icc ((45683 / 512000) : ℝ) (45699 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1195362179 / 1000000000) : ℝ) ≤ Real.exp (2 * (45683 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45683 / 512000)) (1195362179 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45699 / 512000) : ℝ)) ≤ (1195436893 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45699 / 512000)) (1195436893 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((39047826217 / 500000) : ℝ) ≤ Real.exp (3 * (375523 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (375523 / 100000)) (39047826217 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45683 / 512000) : ℝ) (45699 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (375523 / 100000) (751117 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45683 / 512000) (45699 / 512000) (1195362179 / 1000000000) (1195436893 / 1000000000) (375523 / 100000) (751117 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45683 / 512000) (45699 / 512000) (375523 / 100000) (751117 / 200000) (33873 / 1000) (33887 / 1000)
    (28419 / 500) (14261 / 250) (-280817 / 500) (348667 / 1000000) (636591 / 200) (204877 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (375523 / 100000) (39047826217 / 500000) (204877 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (375523 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (375523 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell822 :
    ∀ t ∈ Set.Icc ((45699 / 512000) : ℝ) (9143 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((298859223 / 250000000) : ℝ) ≤ Real.exp (2 * (45699 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45699 / 512000)) (298859223 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9143 / 102400) : ℝ)) ≤ (119551161 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9143 / 102400)) (119551161 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15630098959 / 200000) : ℝ) ≤ Real.exp (3 * (469433 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (469433 / 125000)) (15630098959 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45699 / 512000) : ℝ) (9143 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (469433 / 125000) (187791 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45699 / 512000) (9143 / 102400) (298859223 / 250000000) (119551161 / 100000000) (469433 / 125000) (187791 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45699 / 512000) (9143 / 102400) (469433 / 125000) (187791 / 50000) (33879 / 1000) (8473 / 250)
    (14217 / 250) (2283 / 40) (-561663 / 1000) (348487 / 1000000) (3183751 / 1000) (818933 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (469433 / 125000) (15630098959 / 200000) (818933 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (469433 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (469433 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell823 :
    ∀ t ∈ Set.Icc ((9143 / 102400) : ℝ) (45731 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1195511609 / 1000000000) : ℝ) ≤ Real.exp (2 * (9143 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9143 / 102400)) (1195511609 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45731 / 512000) : ℝ)) ≤ (298896583 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45731 / 512000)) (298896583 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15641122057 / 200000) : ℝ) ≤ Real.exp (3 * (3755699 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3755699 / 1000000)) (15641122057 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9143 / 102400) : ℝ) (45731 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3755699 / 1000000) (751211 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9143 / 102400) (45731 / 512000) (1195511609 / 1000000000) (298896583 / 250000000) (3755699 / 1000000) (751211 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9143 / 102400) (45731 / 512000) (3755699 / 1000000) (751211 / 200000) (8471 / 250) (16949 / 500)
    (28449 / 500) (11421 / 200) (-280849 / 500) (348307 / 1000000) (796137 / 250) (3273423 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3755699 / 1000000) (15641122057 / 200000) (3273423 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3755699 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3755699 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell824 :
    ∀ t ∈ Set.Icc ((45731 / 512000) : ℝ) (45747 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1195586331 / 1000000000) : ℝ) ≤ Real.exp (2 * (45731 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45731 / 512000)) (1195586331 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45747 / 512000) : ℝ)) ≤ (597830529 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45747 / 512000)) (597830529 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15652152929 / 200000) : ℝ) ≤ Real.exp (3 * (1877967 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1877967 / 500000)) (15652152929 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45731 / 512000) : ℝ) (45747 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1877967 / 500000) (3756289 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45731 / 512000) (45747 / 512000) (1195586331 / 1000000000) (597830529 / 500000000) (1877967 / 500000) (3756289 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45731 / 512000) (45747 / 512000) (1877967 / 500000) (3756289 / 1000000) (3389 / 100) (4238 / 125)
    (7116 / 125) (11427 / 200) (-561737 / 1000) (348127 / 1000000) (1592671 / 500) (817779 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1877967 / 500000) (15652152929 / 200000) (817779 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1877967 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1877967 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell825 :
    ∀ t ∈ Set.Icc ((45747 / 512000) : ℝ) (45763 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1195661057 / 1000000000) : ℝ) ≤ Real.exp (2 * (45747 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45747 / 512000)) (1195661057 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45763 / 512000) : ℝ)) ≤ (1195735789 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45763 / 512000)) (1195735789 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((78315957903 / 1000000) : ℝ) ≤ Real.exp (3 * (3756169 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3756169 / 1000000)) (78315957903 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45747 / 512000) : ℝ) (45763 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3756169 / 1000000) (939131 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45747 / 512000) (45763 / 512000) (1195661057 / 1000000000) (1195735789 / 1000000000) (3756169 / 1000000) (939131 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45747 / 512000) (45763 / 512000) (3756169 / 1000000) (939131 / 250000) (4237 / 125) (33909 / 1000)
    (28479 / 500) (11433 / 200) (-561771 / 1000) (347947 / 1000000) (3186139 / 1000) (3268811 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3756169 / 1000000) (78315957903 / 1000000) (3268811 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3756169 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3756169 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell826 :
    ∀ t ∈ Set.Icc ((45763 / 512000) : ℝ) (45779 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((298933947 / 250000000) : ℝ) ≤ Real.exp (2 * (45763 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45763 / 512000)) (298933947 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45779 / 512000) : ℝ)) ≤ (47832421 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45779 / 512000)) (47832421 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((78370954973 / 1000000) : ℝ) ≤ Real.exp (3 * (3756403 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3756403 / 1000000)) (78370954973 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45763 / 512000) : ℝ) (45779 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3756403 / 1000000) (3756759 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45763 / 512000) (45779 / 512000) (298933947 / 250000000) (47832421 / 40000000) (3756403 / 1000000) (3756759 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45763 / 512000) (45779 / 512000) (3756403 / 1000000) (3756759 / 1000000) (33901 / 1000) (6783 / 200)
    (14247 / 250) (11439 / 200) (-2809 / 5) (43471 / 125000) (398367 / 125) (3266517 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3756403 / 1000000) (78370954973 / 1000000) (3266517 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3756403 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3756403 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell827 :
    ∀ t ∈ Set.Icc ((45779 / 512000) : ℝ) (9159 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((298952631 / 250000000) : ℝ) ≤ Real.exp (2 * (45779 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45779 / 512000)) (298952631 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9159 / 102400) : ℝ)) ≤ (597942633 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9159 / 102400)) (597942633 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((39213112971 / 500000) : ℝ) ≤ Real.exp (3 * (1878319 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1878319 / 500000)) (39213112971 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45779 / 512000) : ℝ) (9159 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1878319 / 500000) (1878497 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45779 / 512000) (9159 / 102400) (298952631 / 250000000) (597942633 / 500000000) (1878319 / 500000) (1878497 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45779 / 512000) (9159 / 102400) (1878319 / 500000) (1878497 / 500000) (33907 / 1000) (33921 / 1000)
    (28509 / 500) (2289 / 40) (-112367 / 200) (86897 / 250000) (1593867 / 500) (652843 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1878319 / 500000) (39213112971 / 500000) (652843 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1878319 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1878319 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell828 :
    ∀ t ∈ Set.Icc ((9159 / 102400) : ℝ) (45811 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((239177053 / 200000000) : ℝ) ≤ Real.exp (2 * (9159 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9159 / 102400)) (239177053 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45811 / 512000) : ℝ)) ≤ (1195960011 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45811 / 512000)) (1195960011 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((78481535891 / 1000000) : ℝ) ≤ Real.exp (3 * (3756873 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3756873 / 1000000)) (78481535891 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9159 / 102400) : ℝ) (45811 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3756873 / 1000000) (939307 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9159 / 102400) (45811 / 512000) (239177053 / 200000000) (1195960011 / 1000000000) (3756873 / 1000000) (939307 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9159 / 102400) (45811 / 512000) (3756873 / 1000000) (939307 / 250000) (33913 / 1000) (16963 / 500)
    (57049 / 1000) (11451 / 200) (-561873 / 1000) (21713 / 62500) (398566 / 125) (1630957 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3756873 / 1000000) (78481535891 / 1000000) (1630957 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3756873 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3756873 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell829 :
    ∀ t ∈ Set.Icc ((45811 / 512000) : ℝ) (45827 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((119596001 / 100000000) : ℝ) ≤ Real.exp (2 * (45811 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45811 / 512000)) (119596001 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45827 / 512000) : ℝ)) ≤ (1196034761 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45827 / 512000)) (1196034761 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((78536884847 / 1000000) : ℝ) ≤ Real.exp (3 * (939277 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (939277 / 250000)) (78536884847 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45811 / 512000) : ℝ) (45827 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (939277 / 250000) (3757463 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45811 / 512000) (45827 / 512000) (119596001 / 100000000) (1196034761 / 1000000000) (939277 / 250000) (3757463 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45811 / 512000) (45827 / 512000) (939277 / 250000) (3757463 / 1000000) (16959 / 500) (8483 / 250)
    (57079 / 1000) (11457 / 200) (-561907 / 1000) (86807 / 250000) (1594663 / 500) (651923 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (939277 / 250000) (78536884847 / 1000000) (651923 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (939277 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (939277 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell830 :
    ∀ t ∈ Set.Icc ((45827 / 512000) : ℝ) (45843 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((29900869 / 25000000) : ℝ) ≤ Real.exp (2 * (45827 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45827 / 512000)) (29900869 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45843 / 512000) : ℝ)) ≤ (239221903 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45843 / 512000)) (239221903 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((78592272837 / 1000000) : ℝ) ≤ Real.exp (3 * (3757343 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3757343 / 1000000)) (78592272837 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45827 / 512000) : ℝ) (45843 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3757343 / 1000000) (1878849 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45827 / 512000) (45843 / 512000) (29900869 / 25000000) (239221903 / 200000000) (3757343 / 1000000) (1878849 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45827 / 512000) (45843 / 512000) (3757343 / 1000000) (1878849 / 500000) (8481 / 250) (16969 / 500)
    (57109 / 1000) (14329 / 250) (-280971 / 500) (43381 / 125000) (797531 / 250) (1628659 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3757343 / 1000000) (78592272837 / 1000000) (1628659 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3757343 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3757343 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell831 :
    ∀ t ∈ Set.Icc ((45843 / 512000) : ℝ) (45859 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((598054757 / 500000000) : ℝ) ≤ Real.exp (2 * (45843 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45843 / 512000)) (598054757 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45859 / 512000) : ℝ)) ≤ (598092137 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45859 / 512000)) (598092137 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((7864769989 / 100000) : ℝ) ≤ Real.exp (3 * (1878789 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1878789 / 500000)) (7864769989 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45843 / 512000) : ℝ) (45859 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1878789 / 500000) (3757933 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45843 / 512000) (45859 / 512000) (598054757 / 500000000) (598092137 / 500000000) (1878789 / 500000) (3757933 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45843 / 512000) (45859 / 512000) (1878789 / 500000) (3757933 / 1000000) (33929 / 1000) (33943 / 1000)
    (57139 / 1000) (28673 / 500) (-70247 / 125) (346869 / 1000000) (1595461 / 500) (3255023 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1878789 / 500000) (7864769989 / 100000) (3255023 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1878789 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1878789 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell832 :
    ∀ t ∈ Set.Icc ((45859 / 512000) : ℝ) (367 / 4096), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1196184273 / 1000000000) : ℝ) ≤ Real.exp (2 * (45859 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45859 / 512000)) (1196184273 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((367 / 4096) : ℝ)) ≤ (598129519 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (367 / 4096)) (598129519 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((19675732481 / 250000) : ℝ) ≤ Real.exp (3 * (939453 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (939453 / 250000)) (19675732481 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45859 / 512000) : ℝ) (367 / 4096),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (939453 / 250000) (469771 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45859 / 512000) (367 / 4096) (1196184273 / 1000000000) (598129519 / 500000000) (939453 / 250000) (469771 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45859 / 512000) (367 / 4096) (939453 / 250000) (469771 / 125000) (6787 / 200) (33949 / 1000)
    (57169 / 1000) (7172 / 125) (-112401 / 200) (346691 / 1000000) (79793 / 25) (1626369 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (939453 / 250000) (19675732481 / 250000) (1626369 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (939453 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (939453 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell833 :
    ∀ t ∈ Set.Icc ((367 / 4096) : ℝ) (45891 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1196259037 / 1000000000) : ℝ) ≤ Real.exp (2 * (367 / 4096)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (367 / 4096)) (1196259037 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45891 / 512000) : ℝ)) ≤ (1196333807 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45891 / 512000)) (1196333807 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((39379217509 / 500000) : ℝ) ≤ Real.exp (3 * (3758047 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3758047 / 1000000)) (39379217509 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((367 / 4096) : ℝ) (45891 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3758047 / 1000000) (3758403 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (367 / 4096) (45891 / 512000) (1196259037 / 1000000000) (1196333807 / 1000000000) (3758047 / 1000000) (3758403 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (367 / 4096) (45891 / 512000) (3758047 / 1000000) (3758403 / 1000000) (33941 / 1000) (6791 / 200)
    (57199 / 1000) (28703 / 500) (-562039 / 1000) (346511 / 1000000) (3192519 / 1000) (1625223 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3758047 / 1000000) (39379217509 / 500000) (1625223 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3758047 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3758047 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell834 :
    ∀ t ∈ Set.Icc ((45891 / 512000) : ℝ) (45907 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((598166903 / 500000000) : ℝ) ≤ Real.exp (2 * (45891 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45891 / 512000)) (598166903 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45907 / 512000) : ℝ)) ≤ (59820429 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45907 / 512000)) (59820429 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((9851747407 / 125000) : ℝ) ≤ Real.exp (3 * (1879141 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1879141 / 500000)) (9851747407 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45891 / 512000) : ℝ) (45907 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1879141 / 500000) (1879319 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45891 / 512000) (45907 / 512000) (598166903 / 500000000) (59820429 / 50000000) (1879141 / 500000) (1879319 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45891 / 512000) (45907 / 512000) (1879141 / 500000) (1879319 / 500000) (16973 / 500) (849 / 25)
    (57229 / 1000) (57437 / 1000) (-562073 / 1000) (86583 / 250000) (3193317 / 1000) (649631 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1879141 / 500000) (9851747407 / 125000) (649631 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1879141 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1879141 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell835 :
    ∀ t ∈ Set.Icc ((45907 / 512000) : ℝ) (45923 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1196408579 / 1000000000) : ℝ) ≤ Real.exp (2 * (45907 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45907 / 512000)) (1196408579 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45923 / 512000) : ℝ)) ≤ (598241679 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45923 / 512000)) (598241679 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((78869562667 / 1000000) : ℝ) ≤ Real.exp (3 * (3758517 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3758517 / 1000000)) (78869562667 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45907 / 512000) : ℝ) (45923 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3758517 / 1000000) (3758873 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45907 / 512000) (45923 / 512000) (1196408579 / 1000000000) (598241679 / 500000000) (3758517 / 1000000) (3758873 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45907 / 512000) (45923 / 512000) (3758517 / 1000000) (3758873 / 1000000) (4244 / 125) (16983 / 500)
    (57259 / 1000) (57467 / 1000) (-562107 / 1000) (346153 / 1000000) (798529 / 250) (1622933 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3758517 / 1000000) (78869562667 / 1000000) (1622933 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3758517 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3758517 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell836 :
    ∀ t ∈ Set.Icc ((45923 / 512000) : ℝ) (45939 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1196483357 / 1000000000) : ℝ) ≤ Real.exp (2 * (45923 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45923 / 512000)) (1196483357 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45939 / 512000) : ℝ)) ≤ (59827907 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45939 / 512000)) (59827907 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((39462592639 / 500000) : ℝ) ≤ Real.exp (3 * (117461 / 31250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (117461 / 31250)) (39462592639 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45923 / 512000) : ℝ) (45939 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (117461 / 31250) (939777 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45923 / 512000) (45939 / 512000) (1196483357 / 1000000000) (59827907 / 50000000) (117461 / 31250) (939777 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45923 / 512000) (45939 / 512000) (117461 / 31250) (939777 / 250000) (16979 / 500) (8493 / 250)
    (5729 / 100) (57497 / 1000) (-562141 / 1000) (172987 / 500000) (638983 / 200) (3243579 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (117461 / 31250) (39462592639 / 500000) (3243579 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (117461 / 31250)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (117461 / 31250)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell837 :
    ∀ t ∈ Set.Icc ((45939 / 512000) : ℝ) (9191 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1196558139 / 1000000000) : ℝ) ≤ Real.exp (2 * (45939 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45939 / 512000)) (1196558139 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9191 / 102400) : ℝ)) ≤ (37394779 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9191 / 102400)) (37394779 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((19745211779 / 250000) : ℝ) ≤ Real.exp (3 * (3758987 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3758987 / 1000000)) (19745211779 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45939 / 512000) : ℝ) (9191 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3758987 / 1000000) (3759343 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45939 / 512000) (9191 / 102400) (1196558139 / 1000000000) (37394779 / 31250000) (3758987 / 1000000) (3759343 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45939 / 512000) (9191 / 102400) (3758987 / 1000000) (3759343 / 1000000) (33963 / 1000) (33977 / 1000)
    (1433 / 25) (57527 / 1000) (-22487 / 40) (69159 / 200000) (1597857 / 500) (3241293 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3758987 / 1000000) (19745211779 / 250000) (3241293 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3758987 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3758987 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell838 :
    ∀ t ∈ Set.Icc ((9191 / 102400) : ℝ) (45971 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1196632927 / 1000000000) : ℝ) ≤ Real.exp (2 * (9191 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9191 / 102400)) (1196632927 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45971 / 512000) : ℝ)) ≤ (1196707719 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45971 / 512000)) (1196707719 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((7903654821 / 100000) : ℝ) ≤ Real.exp (3 * (1879611 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1879611 / 500000)) (7903654821 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9191 / 102400) : ℝ) (45971 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1879611 / 500000) (3759577 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9191 / 102400) (45971 / 512000) (1196632927 / 1000000000) (1196707719 / 1000000000) (1879611 / 500000) (3759577 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9191 / 102400) (45971 / 512000) (1879611 / 500000) (3759577 / 1000000) (33969 / 1000) (33983 / 1000)
    (1147 / 20) (57557 / 1000) (-562213 / 1000) (21601 / 62500) (3196509 / 1000) (101219 / 31250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1879611 / 500000) (7903654821 / 100000) (101219 / 31250000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1879611 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1879611 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell839 :
    ∀ t ∈ Set.Icc ((45971 / 512000) : ℝ) (45987 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((598353859 / 500000000) : ℝ) ≤ Real.exp (2 * (45971 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45971 / 512000)) (598353859 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45987 / 512000) : ℝ)) ≤ (299195629 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45987 / 512000)) (299195629 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((79092288587 / 1000000) : ℝ) ≤ Real.exp (3 * (3759457 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3759457 / 1000000)) (79092288587 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45971 / 512000) : ℝ) (45987 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3759457 / 1000000) (939953 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45971 / 512000) (45987 / 512000) (598353859 / 500000000) (299195629 / 250000000) (3759457 / 1000000) (939953 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45971 / 512000) (45987 / 512000) (3759457 / 1000000) (939953 / 250000) (1359 / 40) (33989 / 1000)
    (57381 / 1000) (57587 / 1000) (-562247 / 1000) (345437 / 1000000) (3197309 / 1000) (1618363 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3759457 / 1000000) (79092288587 / 1000000) (1618363 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3759457 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3759457 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch041 :
    ∀ t ∈ Set.Icc ((45667 / 512000) : ℝ) (45987 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell820
      hpThetaDensityLowerExpCompact_cell821)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell822
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell823
      hpThetaDensityLowerExpCompact_cell824)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell825
      hpThetaDensityLowerExpCompact_cell826)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell827
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell828
      hpThetaDensityLowerExpCompact_cell829))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell830
      hpThetaDensityLowerExpCompact_cell831)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell832
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell833
      hpThetaDensityLowerExpCompact_cell834)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell835
      hpThetaDensityLowerExpCompact_cell836)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell837
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell838
      hpThetaDensityLowerExpCompact_cell839)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch041
end HodgeProofHP
