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
theorem hpThetaDensityLowerExpCompact_cell120 :
    ∀ t ∈ Set.Icc ((1027 / 12800) : ℝ) (41081 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174061083 / 1000000000) : ℝ) ≤ Real.exp (2 * (1027 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1027 / 12800)) (1174061083 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41081 / 512000) : ℝ)) ≤ (117406567 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41081 / 512000)) (117406567 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31945563511 / 500000) : ℝ) ≤ Real.exp (3 * (461039 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (461039 / 125000)) (31945563511 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1027 / 12800) : ℝ) (41081 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (461039 / 125000) (737689 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1027 / 12800) (41081 / 512000) (1174061083 / 1000000000) (117406567 / 100000000) (461039 / 125000) (737689 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1027 / 12800) (41081 / 512000) (461039 / 125000) (737689 / 200000) (32283 / 1000) (32289 / 1000)
    (48581 / 1000) (48657 / 1000) (-551717 / 1000) (100933 / 250000) (1480687 / 500) (4006817 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (461039 / 125000) (31945563511 / 500000) (4006817 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461039 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461039 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell121 :
    ∀ t ∈ Set.Icc ((41081 / 512000) : ℝ) (20541 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174065669 / 1000000000) : ℝ) ≤ Real.exp (2 * (41081 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41081 / 512000)) (1174065669 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20541 / 256000) : ℝ)) ≤ (73379391 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20541 / 256000)) (73379391 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31947001093 / 500000) : ℝ) ≤ Real.exp (3 * (3688327 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3688327 / 1000000)) (31947001093 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41081 / 512000) : ℝ) (20541 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3688327 / 1000000) (184423 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41081 / 512000) (20541 / 256000) (1174065669 / 1000000000) (73379391 / 62500000) (3688327 / 1000000) (184423 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41081 / 512000) (20541 / 256000) (3688327 / 1000000) (184423 / 50000) (8071 / 250) (32289 / 1000)
    (48583 / 1000) (48659 / 1000) (-551719 / 1000) (403719 / 1000000) (1480711 / 500) (1001659 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3688327 / 1000000) (31947001093 / 500000) (1001659 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688327 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688327 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell122 :
    ∀ t ∈ Set.Icc ((20541 / 256000) : ℝ) (41083 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((234814051 / 200000000) : ℝ) ≤ Real.exp (2 * (20541 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20541 / 256000)) (234814051 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41083 / 512000) : ℝ)) ≤ (587037421 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41083 / 512000)) (587037421 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63896685789 / 1000000) : ℝ) ≤ Real.exp (3 * (3688341 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3688341 / 1000000)) (63896685789 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20541 / 256000) : ℝ) (41083 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3688341 / 1000000) (1844237 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20541 / 256000) (41083 / 512000) (234814051 / 200000000) (587037421 / 500000000) (3688341 / 1000000) (1844237 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20541 / 256000) (41083 / 512000) (3688341 / 1000000) (1844237 / 500000) (8071 / 250) (3229 / 100)
    (9717 / 200) (48661 / 1000) (-275861 / 500) (403707 / 1000000) (2961467 / 1000) (1001617 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3688341 / 1000000) (63896685789 / 1000000) (1001617 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688341 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688341 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell123 :
    ∀ t ∈ Set.Icc ((41083 / 512000) : ℝ) (10271 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174074841 / 1000000000) : ℝ) ≤ Real.exp (2 * (41083 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41083 / 512000)) (1174074841 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((10271 / 128000) : ℝ)) ≤ (1174079429 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (10271 / 128000)) (1174079429 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15974890301 / 250000) : ℝ) ≤ Real.exp (3 * (922089 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (922089 / 250000)) (15974890301 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41083 / 512000) : ℝ) (10271 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (922089 / 250000) (461061 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41083 / 512000) (10271 / 128000) (1174074841 / 1000000000) (1174079429 / 1000000000) (922089 / 250000) (461061 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41083 / 512000) (10271 / 128000) (922089 / 250000) (461061 / 125000) (8071 / 250) (3229 / 100)
    (48587 / 1000) (24331 / 500) (-551729 / 1000) (403693 / 1000000) (370189 / 125) (250393 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (922089 / 250000) (15974890301 / 250000) (250393 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922089 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922089 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell124 :
    ∀ t ∈ Set.Icc ((10271 / 128000) : ℝ) (8217 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293519857 / 250000000) : ℝ) ≤ Real.exp (2 * (10271 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (10271 / 128000)) (293519857 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8217 / 102400) : ℝ)) ≤ (234816803 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8217 / 102400)) (234816803 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((798778063 / 12500) : ℝ) ≤ Real.exp (3 * (368837 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (368837 / 100000)) (798778063 / 12500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((10271 / 128000) : ℝ) (8217 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (368837 / 100000) (3688503 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (10271 / 128000) (8217 / 102400) (293519857 / 250000000) (234816803 / 200000000) (368837 / 100000) (3688503 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (10271 / 128000) (8217 / 102400) (368837 / 100000) (3688503 / 1000000) (6457 / 200) (3229 / 100)
    (12147 / 250) (6083 / 125) (-551727 / 1000) (403681 / 1000000) (2961561 / 1000) (100153 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (368837 / 100000) (798778063 / 12500) (100153 / 25000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (368837 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (368837 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell125 :
    ∀ t ∈ Set.Icc ((8217 / 102400) : ℝ) (20543 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587042007 / 500000000) : ℝ) ≤ Real.exp (2 * (8217 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8217 / 102400)) (587042007 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20543 / 256000) : ℝ)) ≤ (1174088601 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20543 / 256000)) (1174088601 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6390492899 / 100000) : ℝ) ≤ Real.exp (3 * (57631 / 15625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (57631 / 15625)) (6390492899 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8217 / 102400) : ℝ) (20543 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (57631 / 15625) (3688517 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8217 / 102400) (20543 / 256000) (587042007 / 500000000) (1174088601 / 1000000000) (57631 / 15625) (3688517 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8217 / 102400) (20543 / 256000) (57631 / 15625) (3688517 / 1000000) (6457 / 200) (32291 / 1000)
    (4859 / 100) (24333 / 500) (-55173 / 100) (403669 / 1000000) (1480803 / 500) (4005951 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (57631 / 15625) (6390492899 / 100000) (4005951 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (57631 / 15625)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (57631 / 15625)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell126 :
    ∀ t ∈ Set.Icc ((20543 / 256000) : ℝ) (41087 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((5870443 / 5000000) : ℝ) ≤ Real.exp (2 * (20543 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20543 / 256000)) (5870443 / 5000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41087 / 512000) : ℝ)) ≤ (1174093187 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41087 / 512000)) (1174093187 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2556312191 / 40000) : ℝ) ≤ Real.exp (3 * (3688399 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3688399 / 1000000)) (2556312191 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20543 / 256000) : ℝ) (41087 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3688399 / 1000000) (922133 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20543 / 256000) (41087 / 512000) (5870443 / 5000000) (1174093187 / 1000000000) (3688399 / 1000000) (922133 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20543 / 256000) (41087 / 512000) (3688399 / 1000000) (922133 / 250000) (6457 / 200) (32291 / 1000)
    (6074 / 125) (12167 / 250) (-137933 / 250) (50457 / 125000) (1480827 / 500) (4005771 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3688399 / 1000000) (2556312191 / 40000) (4005771 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688399 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688399 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell127 :
    ∀ t ∈ Set.Icc ((41087 / 512000) : ℝ) (321 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587046593 / 500000000) : ℝ) ≤ Real.exp (2 * (41087 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41087 / 512000)) (587046593 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((321 / 4000) : ℝ)) ≤ (587048887 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (321 / 4000)) (587048887 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31955244479 / 500000) : ℝ) ≤ Real.exp (3 * (3688413 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3688413 / 1000000)) (31955244479 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41087 / 512000) : ℝ) (321 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3688413 / 1000000) (1844273 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41087 / 512000) (321 / 4000) (587046593 / 500000000) (587048887 / 500000000) (3688413 / 1000000) (1844273 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41087 / 512000) (321 / 4000) (3688413 / 1000000) (1844273 / 500000) (16143 / 500) (8073 / 250)
    (48593 / 1000) (48669 / 1000) (-110347 / 200) (403643 / 1000000) (2961699 / 1000) (4005603 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3688413 / 1000000) (31955244479 / 500000) (4005603 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688413 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688413 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell128 :
    ∀ t ∈ Set.Icc ((321 / 4000) : ℝ) (41089 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174097773 / 1000000000) : ℝ) ≤ Real.exp (2 * (321 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (321 / 4000)) (1174097773 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41089 / 512000) : ℝ)) ≤ (29352559 / 25000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41089 / 512000)) (29352559 / 25000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31956682497 / 500000) : ℝ) ≤ Real.exp (3 * (922107 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (922107 / 250000)) (31956682497 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((321 / 4000) : ℝ) (41089 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (922107 / 250000) (46107 / 12500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (321 / 4000) (41089 / 512000) (1174097773 / 1000000000) (29352559 / 25000000) (922107 / 250000) (46107 / 12500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (321 / 4000) (41089 / 512000) (922107 / 250000) (46107 / 12500) (16143 / 500) (8073 / 250)
    (9719 / 200) (48671 / 1000) (-275871 / 500) (40363 / 100000) (370218 / 125) (4005423 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (922107 / 250000) (31956682497 / 500000) (4005423 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922107 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922107 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell129 :
    ∀ t ∈ Set.Icc ((41089 / 512000) : ℝ) (4109 / 51200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174102359 / 1000000000) : ℝ) ≤ Real.exp (2 * (41089 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41089 / 512000)) (1174102359 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4109 / 51200) : ℝ)) ≤ (587053473 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4109 / 51200)) (587053473 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6391604941 / 100000) : ℝ) ≤ Real.exp (3 * (1844221 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1844221 / 500000)) (6391604941 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41089 / 512000) : ℝ) (4109 / 51200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1844221 / 500000) (147543 / 40000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41089 / 512000) (4109 / 51200) (1174102359 / 1000000000) (587053473 / 500000000) (1844221 / 500000) (147543 / 40000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41089 / 512000) (4109 / 51200) (1844221 / 500000) (147543 / 40000) (16143 / 500) (8073 / 250)
    (48597 / 1000) (48673 / 1000) (-27587 / 50) (201809 / 500000) (370224 / 125) (2002627 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1844221 / 500000) (6391604941 / 100000) (2002627 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844221 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844221 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell130 :
    ∀ t ∈ Set.Icc ((4109 / 51200) : ℝ) (41091 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((234821389 / 200000000) : ℝ) ≤ Real.exp (2 * (4109 / 51200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4109 / 51200)) (234821389 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41091 / 512000) : ℝ)) ≤ (1174111533 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41091 / 512000)) (1174111533 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63918733939 / 1000000) : ℝ) ≤ Real.exp (3 * (461057 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (461057 / 125000)) (63918733939 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4109 / 51200) : ℝ) (41091 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (461057 / 125000) (3688589 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (4109 / 51200) (41091 / 512000) (234821389 / 200000000) (1174111533 / 1000000000) (461057 / 125000) (3688589 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (4109 / 51200) (41091 / 512000) (461057 / 125000) (3688589 / 1000000) (32287 / 1000) (32293 / 1000)
    (48599 / 1000) (24337 / 500) (-551743 / 1000) (80721 / 200000) (2961837 / 1000) (2002543 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (461057 / 125000) (63918733939 / 1000000) (2002543 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461057 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461057 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell131 :
    ∀ t ∈ Set.Icc ((41091 / 512000) : ℝ) (10273 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293527883 / 250000000) : ℝ) ≤ Real.exp (2 * (41091 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41091 / 512000)) (293527883 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((10273 / 128000) : ℝ)) ≤ (1174116119 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (10273 / 128000)) (1174116119 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31960805173 / 500000) : ℝ) ≤ Real.exp (3 * (3688471 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3688471 / 1000000)) (31960805173 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41091 / 512000) : ℝ) (10273 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3688471 / 1000000) (922151 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41091 / 512000) (10273 / 128000) (293527883 / 250000000) (1174116119 / 1000000000) (3688471 / 1000000) (922151 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41091 / 512000) (10273 / 128000) (3688471 / 1000000) (922151 / 250000) (32287 / 1000) (32293 / 1000)
    (243 / 5) (12169 / 250) (-110349 / 200) (50449 / 125000) (592377 / 200) (2002453 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3688471 / 1000000) (31960805173 / 500000) (2002453 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688471 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688471 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell132 :
    ∀ t ∈ Set.Icc ((10273 / 128000) : ℝ) (41093 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587058059 / 500000000) : ℝ) ≤ Real.exp (2 * (10273 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (10273 / 128000)) (587058059 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41093 / 512000) : ℝ)) ≤ (234824141 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41093 / 512000)) (234824141 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63924295109 / 1000000) : ℝ) ≤ Real.exp (3 * (737697 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (737697 / 200000)) (63924295109 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((10273 / 128000) : ℝ) (41093 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (737697 / 200000) (1844309 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (10273 / 128000) (41093 / 512000) (587058059 / 500000000) (234824141 / 200000000) (737697 / 200000) (1844309 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (10273 / 128000) (41093 / 512000) (737697 / 200000) (1844309 / 500000) (32287 / 1000) (32293 / 1000)
    (24301 / 500) (24339 / 500) (-137937 / 250) (20179 / 50000) (296193 / 100) (2002369 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (737697 / 200000) (63924295109 / 1000000) (2002369 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (737697 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (737697 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell133 :
    ∀ t ∈ Set.Icc ((41093 / 512000) : ℝ) (20547 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((4586409 / 3906250) : ℝ) ≤ Real.exp (2 * (41093 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41093 / 512000)) (4586409 / 3906250) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20547 / 256000) : ℝ)) ≤ (293531323 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20547 / 256000)) (293531323 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((12785434353 / 200000) : ℝ) ≤ Real.exp (3 * (7377 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (7377 / 2000)) (12785434353 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41093 / 512000) : ℝ) (20547 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (7377 / 2000) (3688633 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41093 / 512000) (20547 / 256000) (4586409 / 3906250) (293531323 / 250000000) (7377 / 2000) (3688633 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41093 / 512000) (20547 / 256000) (7377 / 2000) (3688633 / 1000000) (4036 / 125) (16147 / 500)
    (12151 / 250) (1217 / 25) (-551751 / 1000) (201783 / 500000) (1480989 / 500) (4004557 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (7377 / 2000) (12785434353 / 200000) (4004557 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7377 / 2000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7377 / 2000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell134 :
    ∀ t ∈ Set.Icc ((20547 / 256000) : ℝ) (8219 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174125291 / 1000000000) : ℝ) ≤ Real.exp (2 * (20547 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20547 / 256000)) (1174125291 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8219 / 102400) : ℝ)) ≤ (587064939 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8219 / 102400)) (587064939 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31964928381 / 500000) : ℝ) ≤ Real.exp (3 * (1844257 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1844257 / 500000)) (31964928381 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20547 / 256000) : ℝ) (8219 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1844257 / 500000) (3688647 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20547 / 256000) (8219 / 102400) (1174125291 / 1000000000) (587064939 / 500000000) (1844257 / 500000) (3688647 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20547 / 256000) (8219 / 102400) (1844257 / 500000) (3688647 / 1000000) (4036 / 125) (16147 / 500)
    (24303 / 500) (48681 / 1000) (-551753 / 1000) (201777 / 500000) (2962023 / 1000) (4004389 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1844257 / 500000) (31964928381 / 500000) (4004389 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844257 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844257 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell135 :
    ∀ t ∈ Set.Icc ((8219 / 102400) : ℝ) (5137 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174129877 / 1000000000) : ℝ) ≤ Real.exp (2 * (8219 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8219 / 102400)) (1174129877 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((5137 / 64000) : ℝ)) ≤ (234826893 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (5137 / 64000)) (234826893 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63932733669 / 1000000) : ℝ) ≤ Real.exp (3 * (3688529 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3688529 / 1000000)) (63932733669 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8219 / 102400) : ℝ) (5137 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3688529 / 1000000) (3688661 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8219 / 102400) (5137 / 64000) (1174129877 / 1000000000) (234826893 / 200000000) (3688529 / 1000000) (3688661 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8219 / 102400) (5137 / 64000) (3688529 / 1000000) (3688661 / 1000000) (32289 / 1000) (16147 / 500)
    (6076 / 125) (48683 / 1000) (-13794 / 25) (403541 / 1000000) (740517 / 250) (4004209 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3688529 / 1000000) (63932733669 / 1000000) (4004209 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688529 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688529 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell136 :
    ∀ t ∈ Set.Icc ((5137 / 64000) : ℝ) (41097 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((18345851 / 15625000) : ℝ) ≤ Real.exp (2 * (5137 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (5137 / 64000)) (18345851 / 15625000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41097 / 512000) : ℝ)) ≤ (1174139051 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41097 / 512000)) (1174139051 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63935418899 / 1000000) : ℝ) ≤ Real.exp (3 * (3688543 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3688543 / 1000000)) (63935418899 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((5137 / 64000) : ℝ) (41097 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3688543 / 1000000) (922169 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (5137 / 64000) (41097 / 512000) (18345851 / 15625000) (1174139051 / 1000000000) (3688543 / 1000000) (922169 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (5137 / 64000) (41097 / 512000) (3688543 / 1000000) (922169 / 250000) (32289 / 1000) (6459 / 200)
    (48609 / 1000) (9737 / 200) (-275879 / 500) (403529 / 1000000) (740529 / 250) (4004041 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3688543 / 1000000) (63935418899 / 1000000) (4004041 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688543 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688543 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell137 :
    ∀ t ∈ Set.Icc ((41097 / 512000) : ℝ) (20549 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((23482781 / 20000000) : ℝ) ≤ Real.exp (2 * (41097 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41097 / 512000)) (23482781 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20549 / 256000) : ℝ)) ≤ (587071819 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20549 / 256000)) (587071819 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31969052121 / 500000) : ℝ) ≤ Real.exp (3 * (3688557 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3688557 / 1000000)) (31969052121 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41097 / 512000) : ℝ) (20549 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3688557 / 1000000) (368869 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41097 / 512000) (20549 / 256000) (23482781 / 20000000) (587071819 / 500000000) (3688557 / 1000000) (368869 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41097 / 512000) (20549 / 256000) (3688557 / 1000000) (368869 / 100000) (32289 / 1000) (6459 / 200)
    (48611 / 1000) (48687 / 1000) (-551761 / 1000) (100879 / 250000) (2962161 / 1000) (4003873 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3688557 / 1000000) (31969052121 / 500000) (4003873 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688557 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688557 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell138 :
    ∀ t ∈ Set.Icc ((20549 / 256000) : ℝ) (41099 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174143637 / 1000000000) : ℝ) ≤ Real.exp (2 * (20549 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20549 / 256000)) (1174143637 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41099 / 512000) : ℝ)) ≤ (9173033 / 7812500) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41099 / 512000)) (9173033 / 7812500) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((799262269 / 12500) : ℝ) ≤ Real.exp (3 * (922143 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (922143 / 250000)) (799262269 / 12500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20549 / 256000) : ℝ) (41099 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (922143 / 250000) (737741 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20549 / 256000) (41099 / 512000) (1174143637 / 1000000000) (9173033 / 7812500) (922143 / 250000) (737741 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20549 / 256000) (41099 / 512000) (922143 / 250000) (737741 / 200000) (3229 / 100) (6459 / 200)
    (48613 / 1000) (6086 / 125) (-551763 / 1000) (403503 / 1000000) (2962209 / 1000) (4003693 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (922143 / 250000) (799262269 / 12500) (4003693 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922143 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922143 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell139 :
    ∀ t ∈ Set.Icc ((41099 / 512000) : ℝ) (411 / 5120), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174148223 / 1000000000) : ℝ) ≤ Real.exp (2 * (41099 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41099 / 512000)) (1174148223 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((411 / 5120) : ℝ)) ≤ (1174152811 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (411 / 5120)) (1174152811 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((7992958387 / 125000) : ℝ) ≤ Real.exp (3 * (1844293 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1844293 / 500000)) (7992958387 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41099 / 512000) : ℝ) (411 / 5120),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1844293 / 500000) (3688719 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41099 / 512000) (411 / 5120) (1174148223 / 1000000000) (1174152811 / 1000000000) (1844293 / 500000) (3688719 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41099 / 512000) (411 / 5120) (1844293 / 500000) (3688719 / 1000000) (3229 / 100) (4037 / 125)
    (24307 / 500) (4869 / 100) (-275883 / 500) (403491 / 1000000) (1481127 / 500) (1000881 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1844293 / 500000) (7992958387 / 125000) (1000881 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844293 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844293 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch006 :
    ∀ t ∈ Set.Icc ((1027 / 12800) : ℝ) (411 / 5120),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell120
      hpThetaDensityLowerExpCompact_cell121)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell122
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell123
      hpThetaDensityLowerExpCompact_cell124)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell125
      hpThetaDensityLowerExpCompact_cell126)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell127
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell128
      hpThetaDensityLowerExpCompact_cell129))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell130
      hpThetaDensityLowerExpCompact_cell131)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell132
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell133
      hpThetaDensityLowerExpCompact_cell134)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell135
      hpThetaDensityLowerExpCompact_cell136)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell137
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell138
      hpThetaDensityLowerExpCompact_cell139)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch006
end HodgeProofHP
