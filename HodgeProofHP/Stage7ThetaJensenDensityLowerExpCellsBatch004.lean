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
theorem hpThetaDensityLowerExpCompact_cell080 :
    ∀ t ∈ Set.Icc ((513 / 6400) : ℝ) (41041 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((23477553 / 20000000) : ℝ) ≤ Real.exp (2 * (513 / 6400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (513 / 6400)) (23477553 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41041 / 512000) : ℝ)) ≤ (293470559 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41041 / 512000)) (293470559 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63780818537 / 1000000) : ℝ) ≤ Real.exp (3 * (460967 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (460967 / 125000)) (63780818537 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((513 / 6400) : ℝ) (41041 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (460967 / 125000) (3687869 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (513 / 6400) (41041 / 512000) (23477553 / 20000000) (293470559 / 250000000) (460967 / 125000) (3687869 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (513 / 6400) (41041 / 512000) (460967 / 125000) (3687869 / 1000000) (3227 / 100) (8069 / 250)
    (6064 / 125) (12147 / 250) (-551613 / 1000) (404241 / 1000000) (118381 / 40) (2006873 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (460967 / 125000) (63780818537 / 1000000) (2006873 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (460967 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (460967 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell081 :
    ∀ t ∈ Set.Icc ((41041 / 512000) : ℝ) (20521 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((234776447 / 200000000) : ℝ) ≤ Real.exp (2 * (41041 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41041 / 512000)) (234776447 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20521 / 256000) : ℝ)) ≤ (586943411 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20521 / 256000)) (586943411 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63783688737 / 1000000) : ℝ) ≤ Real.exp (3 * (3687751 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3687751 / 1000000)) (63783688737 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41041 / 512000) : ℝ) (20521 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3687751 / 1000000) (3687883 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41041 / 512000) (20521 / 256000) (234776447 / 200000000) (586943411 / 500000000) (3687751 / 1000000) (3687883 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41041 / 512000) (20521 / 256000) (3687751 / 1000000) (3687883 / 1000000) (3227 / 100) (8069 / 250)
    (24257 / 500) (48589 / 1000) (-27581 / 50) (101057 / 250000) (295957 / 100) (2006783 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3687751 / 1000000) (63783688737 / 1000000) (2006783 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687751 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687751 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell082 :
    ∀ t ∈ Set.Icc ((20521 / 256000) : ℝ) (41043 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173886821 / 1000000000) : ℝ) ≤ Real.exp (2 * (20521 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20521 / 256000)) (1173886821 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41043 / 512000) : ℝ)) ≤ (1173891407 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41043 / 512000)) (1173891407 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63786367707 / 1000000) : ℝ) ≤ Real.exp (3 * (737553 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (737553 / 200000)) (63786367707 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20521 / 256000) : ℝ) (41043 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (737553 / 200000) (1843949 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20521 / 256000) (41043 / 512000) (1173886821 / 1000000000) (1173891407 / 1000000000) (737553 / 200000) (1843949 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20521 / 256000) (41043 / 512000) (737553 / 200000) (1843949 / 500000) (32271 / 1000) (8069 / 250)
    (12129 / 250) (48591 / 1000) (-275809 / 500) (50527 / 125000) (1479809 / 500) (4013397 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (737553 / 200000) (63786367707 / 1000000) (4013397 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (737553 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (737553 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell083 :
    ∀ t ∈ Set.Icc ((41043 / 512000) : ℝ) (10261 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((586945703 / 500000000) : ℝ) ≤ Real.exp (2 * (41043 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41043 / 512000)) (586945703 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((10261 / 128000) : ℝ)) ≤ (1173895993 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (10261 / 128000)) (1173895993 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63789046789 / 1000000) : ℝ) ≤ Real.exp (3 * (3687779 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3687779 / 1000000)) (63789046789 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41043 / 512000) : ℝ) (10261 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3687779 / 1000000) (460989 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41043 / 512000) (10261 / 128000) (586945703 / 500000000) (1173895993 / 1000000000) (3687779 / 1000000) (460989 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41043 / 512000) (10261 / 128000) (3687779 / 1000000) (460989 / 125000) (32271 / 1000) (32277 / 1000)
    (48517 / 1000) (48593 / 1000) (-551621 / 1000) (404203 / 1000000) (2959663 / 1000) (4013229 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3687779 / 1000000) (63789046789 / 1000000) (4013229 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687779 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687779 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell084 :
    ∀ t ∈ Set.Icc ((10261 / 128000) : ℝ) (8209 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((146736999 / 125000000) : ℝ) ≤ Real.exp (2 * (10261 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (10261 / 128000)) (146736999 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8209 / 102400) : ℝ)) ≤ (586950289 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8209 / 102400)) (586950289 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((797398967 / 12500) : ℝ) ≤ Real.exp (3 * (1843897 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1843897 / 500000)) (797398967 / 12500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((10261 / 128000) : ℝ) (8209 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1843897 / 500000) (3687927 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (10261 / 128000) (8209 / 102400) (146736999 / 125000000) (586950289 / 500000000) (1843897 / 500000) (3687927 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (10261 / 128000) (8209 / 102400) (1843897 / 500000) (3687927 / 1000000) (32271 / 1000) (32277 / 1000)
    (48519 / 1000) (9719 / 200) (-68953 / 125) (40419 / 100000) (2959711 / 1000) (501631 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1843897 / 500000) (797398967 / 12500) (501631 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843897 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843897 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell085 :
    ∀ t ∈ Set.Icc ((8209 / 102400) : ℝ) (20523 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173900577 / 1000000000) : ℝ) ≤ Real.exp (2 * (8209 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8209 / 102400)) (1173900577 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20523 / 256000) : ℝ)) ≤ (293476291 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20523 / 256000)) (293476291 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2551783867 / 40000) : ℝ) ≤ Real.exp (3 * (57622 / 15625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (57622 / 15625)) (2551783867 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8209 / 102400) : ℝ) (20523 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (57622 / 15625) (3687941 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8209 / 102400) (20523 / 256000) (1173900577 / 1000000000) (293476291 / 250000000) (57622 / 15625) (3687941 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8209 / 102400) (20523 / 256000) (57622 / 15625) (3687941 / 1000000) (4034 / 125) (32277 / 1000)
    (48521 / 1000) (48597 / 1000) (-275813 / 500) (202089 / 500000) (739939 / 250) (50161 / 12500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (57622 / 15625) (2551783867 / 40000) (50161 / 12500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (57622 / 15625)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (57622 / 15625)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell086 :
    ∀ t ∈ Set.Icc ((20523 / 256000) : ℝ) (41047 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173905163 / 1000000000) : ℝ) ≤ Real.exp (2 * (20523 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20523 / 256000)) (1173905163 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41047 / 512000) : ℝ)) ≤ (4695639 / 4000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41047 / 512000)) (4695639 / 4000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((7974683437 / 125000) : ℝ) ≤ Real.exp (3 * (3687823 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3687823 / 1000000)) (7974683437 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20523 / 256000) : ℝ) (41047 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3687823 / 1000000) (737591 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20523 / 256000) (41047 / 512000) (1173905163 / 1000000000) (4695639 / 4000000) (3687823 / 1000000) (737591 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20523 / 256000) (41047 / 512000) (3687823 / 1000000) (737591 / 200000) (4034 / 125) (16139 / 500)
    (48523 / 1000) (24299 / 500) (-551633 / 1000) (101041 / 250000) (2959801 / 1000) (4012699 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3687823 / 1000000) (7974683437 / 125000) (4012699 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687823 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687823 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell087 :
    ∀ t ∈ Set.Icc ((41047 / 512000) : ℝ) (5131 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173909749 / 1000000000) : ℝ) ≤ Real.exp (2 * (41047 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41047 / 512000)) (1173909749 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((5131 / 64000) : ℝ)) ≤ (234782867 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (5131 / 64000)) (234782867 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15950036761 / 250000) : ℝ) ≤ Real.exp (3 * (3687837 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3687837 / 1000000)) (15950036761 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41047 / 512000) : ℝ) (5131 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3687837 / 1000000) (368797 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41047 / 512000) (5131 / 64000) (1173909749 / 1000000000) (234782867 / 200000000) (3687837 / 1000000) (368797 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41047 / 512000) (5131 / 64000) (3687837 / 1000000) (368797 / 100000) (4034 / 125) (16139 / 500)
    (12131 / 250) (243 / 5) (-551631 / 1000) (50519 / 125000) (2959849 / 1000) (401253 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3687837 / 1000000) (15950036761 / 250000) (401253 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687837 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687837 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell088 :
    ∀ t ∈ Set.Icc ((5131 / 64000) : ℝ) (41049 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((586957167 / 500000000) : ℝ) ≤ Real.exp (2 * (5131 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (5131 / 64000)) (586957167 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41049 / 512000) : ℝ)) ≤ (1173918921 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41049 / 512000)) (1173918921 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31901413353 / 500000) : ℝ) ≤ Real.exp (3 * (3687851 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3687851 / 1000000)) (31901413353 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((5131 / 64000) : ℝ) (41049 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3687851 / 1000000) (230499 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (5131 / 64000) (41049 / 512000) (586957167 / 500000000) (1173918921 / 1000000000) (3687851 / 1000000) (230499 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (5131 / 64000) (41049 / 512000) (3687851 / 1000000) (230499 / 62500) (32273 / 1000) (16139 / 500)
    (24263 / 500) (24301 / 500) (-275817 / 500) (20207 / 50000) (1479947 / 500) (2006181 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3687851 / 1000000) (31901413353 / 500000) (2006181 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687851 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687851 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell089 :
    ∀ t ∈ Set.Icc ((41049 / 512000) : ℝ) (821 / 10240), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((29347973 / 25000000) : ℝ) ≤ Real.exp (2 * (41049 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41049 / 512000)) (29347973 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((821 / 10240) : ℝ)) ≤ (586961753 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (821 / 10240)) (586961753 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((7975712237 / 125000) : ℝ) ≤ Real.exp (3 * (1843933 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1843933 / 500000)) (7975712237 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41049 / 512000) : ℝ) (821 / 10240),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1843933 / 500000) (3687999 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41049 / 512000) (821 / 10240) (29347973 / 25000000) (586961753 / 500000000) (1843933 / 500000) (3687999 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41049 / 512000) (821 / 10240) (1843933 / 500000) (3687999 / 1000000) (32273 / 1000) (32279 / 1000)
    (6066 / 125) (12151 / 250) (-551637 / 1000) (202063 / 500000) (1479971 / 500) (4012181 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1843933 / 500000) (7975712237 / 125000) (4012181 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843933 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843933 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell090 :
    ∀ t ∈ Set.Icc ((821 / 10240) : ℝ) (41051 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((234784701 / 200000000) : ℝ) ≤ Real.exp (2 * (821 / 10240)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (821 / 10240)) (234784701 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41051 / 512000) : ℝ)) ≤ (293482023 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41051 / 512000)) (293482023 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63808377791 / 1000000) : ℝ) ≤ Real.exp (3 * (92197 / 25000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (92197 / 25000)) (63808377791 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((821 / 10240) : ℝ) (41051 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (92197 / 25000) (3688013 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (821 / 10240) (41051 / 512000) (234784701 / 200000000) (293482023 / 250000000) (92197 / 25000) (3688013 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (821 / 10240) (41051 / 512000) (92197 / 25000) (3688013 / 1000000) (32273 / 1000) (32279 / 1000)
    (48529 / 1000) (9721 / 200) (-551639 / 1000) (202057 / 500000) (2959987 / 1000) (4012013 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (92197 / 25000) (63808377791 / 1000000) (4012013 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (92197 / 25000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (92197 / 25000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell091 :
    ∀ t ∈ Set.Icc ((41051 / 512000) : ℝ) (10263 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173928091 / 1000000000) : ℝ) ≤ Real.exp (2 * (41051 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41051 / 512000)) (1173928091 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((10263 / 128000) : ℝ)) ≤ (586966339 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (10263 / 128000)) (586966339 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63811249231 / 1000000) : ℝ) ≤ Real.exp (3 * (737579 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (737579 / 200000)) (63811249231 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41051 / 512000) : ℝ) (10263 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (737579 / 200000) (3688027 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41051 / 512000) (10263 / 128000) (1173928091 / 1000000000) (586966339 / 500000000) (737579 / 200000) (3688027 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41051 / 512000) (10263 / 128000) (737579 / 200000) (3688027 / 1000000) (16137 / 500) (32279 / 1000)
    (48531 / 1000) (48607 / 1000) (-275823 / 500) (4041 / 10000) (370004 / 125) (501479 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (737579 / 200000) (63811249231 / 1000000) (501479 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (737579 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (737579 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell092 :
    ∀ t ∈ Set.Icc ((10263 / 128000) : ℝ) (41053 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173932677 / 1000000000) : ℝ) ≤ Real.exp (2 * (10263 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (10263 / 128000)) (1173932677 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41053 / 512000) : ℝ)) ≤ (1173937263 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41053 / 512000)) (1173937263 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63813929359 / 1000000) : ℝ) ≤ Real.exp (3 * (3687909 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3687909 / 1000000)) (63813929359 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((10263 / 128000) : ℝ) (41053 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3687909 / 1000000) (1844021 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (10263 / 128000) (41053 / 512000) (1173932677 / 1000000000) (1173937263 / 1000000000) (3687909 / 1000000) (1844021 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (10263 / 128000) (41053 / 512000) (3687909 / 1000000) (1844021 / 500000) (16137 / 500) (807 / 25)
    (48533 / 1000) (48609 / 1000) (-137911 / 250) (50511 / 125000) (74002 / 25) (250729 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3687909 / 1000000) (63813929359 / 1000000) (250729 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687909 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687909 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell093 :
    ∀ t ∈ Set.Icc ((41053 / 512000) : ℝ) (20527 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((586968631 / 500000000) : ℝ) ≤ Real.exp (2 * (41053 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41053 / 512000)) (586968631 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20527 / 256000) : ℝ)) ≤ (1173941849 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20527 / 256000)) (1173941849 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63816609599 / 1000000) : ℝ) ≤ Real.exp (3 * (3687923 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3687923 / 1000000)) (63816609599 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41053 / 512000) : ℝ) (20527 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3687923 / 1000000) (461007 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41053 / 512000) (20527 / 256000) (586968631 / 500000000) (1173941849 / 1000000000) (3687923 / 1000000) (461007 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41053 / 512000) (20527 / 256000) (3687923 / 1000000) (461007 / 125000) (16137 / 500) (807 / 25)
    (9707 / 200) (4861 / 100) (-551647 / 1000) (101019 / 250000) (23681 / 8) (802299 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3687923 / 1000000) (63816609599 / 1000000) (802299 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687923 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687923 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell094 :
    ∀ t ∈ Set.Icc ((20527 / 256000) : ℝ) (8211 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((146742731 / 125000000) : ℝ) ≤ Real.exp (2 * (20527 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20527 / 256000)) (146742731 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8211 / 102400) : ℝ)) ≤ (234789287 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8211 / 102400)) (234789287 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6381948141 / 100000) : ℝ) ≤ Real.exp (3 * (1843969 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1843969 / 500000)) (6381948141 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20527 / 256000) : ℝ) (8211 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1843969 / 500000) (3688071 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20527 / 256000) (8211 / 102400) (146742731 / 125000000) (234789287 / 200000000) (1843969 / 500000) (3688071 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20527 / 256000) (8211 / 102400) (1843969 / 500000) (3688071 / 1000000) (1291 / 40) (807 / 25)
    (6067 / 125) (12153 / 250) (-11033 / 20) (404063 / 1000000) (2960173 / 1000) (802263 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1843969 / 500000) (6381948141 / 100000) (802263 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843969 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1843969 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell095 :
    ∀ t ∈ Set.Icc ((8211 / 102400) : ℝ) (1283 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((586973217 / 500000000) : ℝ) ≤ Real.exp (2 * (8211 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8211 / 102400)) (586973217 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1283 / 16000) : ℝ)) ≤ (1173951021 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1283 / 16000)) (1173951021 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63822161883 / 1000000) : ℝ) ≤ Real.exp (3 * (230497 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (230497 / 62500)) (63822161883 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8211 / 102400) : ℝ) (1283 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (230497 / 62500) (737617 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8211 / 102400) (1283 / 16000) (586973217 / 500000000) (1173951021 / 1000000000) (230497 / 62500) (737617 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8211 / 102400) (1283 / 16000) (230497 / 62500) (737617 / 200000) (1291 / 40) (32281 / 1000)
    (24269 / 500) (24307 / 500) (-137913 / 250) (8081 / 20000) (1480109 / 500) (2005573 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (230497 / 62500) (63822161883 / 1000000) (2005573 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (230497 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (230497 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell096 :
    ∀ t ∈ Set.Icc ((1283 / 16000) : ℝ) (41057 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((58697551 / 50000000) : ℝ) ≤ Real.exp (2 * (1283 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1283 / 16000)) (58697551 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41057 / 512000) : ℝ)) ≤ (586977803 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41057 / 512000)) (586977803 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63825033943 / 1000000) : ℝ) ≤ Real.exp (3 * (3687967 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3687967 / 1000000)) (63825033943 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1283 / 16000) : ℝ) (41057 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3687967 / 1000000) (3688099 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1283 / 16000) (41057 / 512000) (58697551 / 50000000) (586977803 / 500000000) (3687967 / 1000000) (3688099 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1283 / 16000) (41057 / 512000) (3687967 / 1000000) (3688099 / 1000000) (1291 / 40) (32281 / 1000)
    (2427 / 50) (9723 / 200) (-551659 / 1000) (404037 / 1000000) (2960263 / 1000) (2005483 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3687967 / 1000000) (63825033943 / 1000000) (2005483 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687967 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687967 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell097 :
    ∀ t ∈ Set.Icc ((41057 / 512000) : ℝ) (20529 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((234791121 / 200000000) : ℝ) ≤ Real.exp (2 * (41057 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41057 / 512000)) (234791121 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20529 / 256000) : ℝ)) ≤ (2292891 / 1953125) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20529 / 256000)) (2292891 / 1953125) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1276554293 / 20000) : ℝ) ≤ Real.exp (3 * (3687981 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3687981 / 1000000)) (1276554293 / 20000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41057 / 512000) : ℝ) (20529 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3687981 / 1000000) (1844057 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41057 / 512000) (20529 / 256000) (234791121 / 200000000) (2292891 / 1953125) (3687981 / 1000000) (1844057 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41057 / 512000) (20529 / 256000) (3687981 / 1000000) (1844057 / 500000) (8069 / 250) (32281 / 1000)
    (24271 / 500) (48617 / 1000) (-551657 / 1000) (16161 / 40000) (2960311 / 1000) (4010797 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3687981 / 1000000) (1276554293 / 20000) (4010797 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687981 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3687981 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell098 :
    ∀ t ∈ Set.Icc ((20529 / 256000) : ℝ) (41059 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173960191 / 1000000000) : ℝ) ≤ Real.exp (2 * (20529 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20529 / 256000)) (1173960191 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41059 / 512000) : ℝ)) ≤ (586982389 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41059 / 512000)) (586982389 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63830395469 / 1000000) : ℝ) ≤ Real.exp (3 * (737599 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (737599 / 200000)) (63830395469 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20529 / 256000) : ℝ) (41059 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (737599 / 200000) (57627 / 15625) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20529 / 256000) (41059 / 512000) (1173960191 / 1000000000) (586982389 / 500000000) (737599 / 200000) (57627 / 15625) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20529 / 256000) (41059 / 512000) (737599 / 200000) (57627 / 15625) (8069 / 250) (16141 / 500)
    (48543 / 1000) (48619 / 1000) (-27583 / 50) (101003 / 250000) (740089 / 250) (4010629 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (737599 / 200000) (63830395469 / 1000000) (4010629 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (737599 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (737599 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell099 :
    ∀ t ∈ Set.Icc ((41059 / 512000) : ℝ) (2053 / 25600), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173964777 / 1000000000) : ℝ) ≤ Real.exp (2 * (41059 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41059 / 512000)) (1173964777 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2053 / 25600) : ℝ)) ≤ (293492341 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2053 / 25600)) (293492341 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((638332679 / 10000) : ℝ) ≤ Real.exp (3 * (368801 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (368801 / 100000)) (638332679 / 10000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41059 / 512000) : ℝ) (2053 / 25600),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (368801 / 100000) (3688143 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41059 / 512000) (2053 / 25600) (1173964777 / 1000000000) (293492341 / 250000000) (368801 / 100000) (3688143 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41059 / 512000) (2053 / 25600) (368801 / 100000) (3688143 / 1000000) (8069 / 250) (16141 / 500)
    (9709 / 200) (48621 / 1000) (-275831 / 500) (403999 / 1000000) (592081 / 200) (250653 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (368801 / 100000) (638332679 / 10000) (250653 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (368801 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (368801 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch004 :
    ∀ t ∈ Set.Icc ((513 / 6400) : ℝ) (2053 / 25600),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell080
      hpThetaDensityLowerExpCompact_cell081)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell082
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell083
      hpThetaDensityLowerExpCompact_cell084)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell085
      hpThetaDensityLowerExpCompact_cell086)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell087
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell088
      hpThetaDensityLowerExpCompact_cell089))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell090
      hpThetaDensityLowerExpCompact_cell091)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell092
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell093
      hpThetaDensityLowerExpCompact_cell094)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell095
      hpThetaDensityLowerExpCompact_cell096)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell097
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell098
      hpThetaDensityLowerExpCompact_cell099)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch004
end HodgeProofHP
