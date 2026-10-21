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
theorem hpThetaDensityLowerExpCompact_cell960 :
    ∀ t ∈ Set.Icc ((49427 / 512000) : ℝ) (49459 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((242594563 / 200000000) : ℝ) ≤ Real.exp (2 * (49427 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49427 / 512000)) (242594563 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((49459 / 512000) : ℝ)) ≤ (1213124447 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49459 / 512000)) (1213124447 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((92195034017 / 1000000) : ℝ) ≤ Real.exp (3 * (1905277 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1905277 / 500000)) (92195034017 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((49427 / 512000) : ℝ) (49459 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1905277 / 500000) (238197 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (49427 / 512000) (49459 / 512000) (242594563 / 200000000) (1213124447 / 1000000000) (1905277 / 500000) (238197 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (49427 / 512000) (49459 / 512000) (1905277 / 500000) (238197 / 62500) (17607 / 500) (35237 / 1000)
    (12811 / 200) (6441 / 100) (-567749 / 1000) (6173 / 20000) (675111 / 200) (2776723 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1905277 / 500000) (92195034017 / 1000000) (2776723 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1905277 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1905277 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell961 :
    ∀ t ∈ Set.Icc ((49459 / 512000) : ℝ) (49491 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((606562223 / 500000000) : ℝ) ≤ Real.exp (2 * (49459 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49459 / 512000)) (606562223 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((49491 / 512000) : ℝ)) ≤ (1213276097 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49491 / 512000)) (1213276097 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((46163391231 / 500000) : ℝ) ≤ Real.exp (3 * (381103 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (381103 / 100000)) (46163391231 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((49459 / 512000) : ℝ) (49491 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (381103 / 100000) (3811629 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (49459 / 512000) (49491 / 512000) (606562223 / 500000000) (1213276097 / 1000000000) (381103 / 100000) (3811629 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (49459 / 512000) (49491 / 512000) (381103 / 100000) (3811629 / 1000000) (17613 / 500) (4406 / 125)
    (64119 / 1000) (2579 / 40) (-567799 / 1000) (12333 / 40000) (675449 / 200) (69319 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (381103 / 100000) (46163391231 / 500000) (69319 / 25000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (381103 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (381103 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell962 :
    ∀ t ∈ Set.Icc ((49491 / 512000) : ℝ) (49523 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((18957439 / 15625000) : ℝ) ≤ Real.exp (2 * (49491 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49491 / 512000)) (18957439 / 15625000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((49523 / 512000) : ℝ)) ≤ (606713883 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49523 / 512000)) (606713883 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((92458719177 / 1000000) : ℝ) ≤ Real.exp (3 * (1905753 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1905753 / 500000)) (92458719177 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((49491 / 512000) : ℝ) (49523 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1905753 / 500000) (762421 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (49491 / 512000) (49523 / 512000) (18957439 / 15625000) (606713883 / 500000000) (1905753 / 500000) (762421 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (49491 / 512000) (49523 / 512000) (1905753 / 500000) (762421 / 200000) (35237 / 1000) (1763 / 50)
    (64183 / 1000) (64539 / 1000) (-283927 / 500) (77 / 250) (844733 / 250) (692201 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1905753 / 500000) (92458719177 / 1000000) (692201 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1905753 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1905753 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell963 :
    ∀ t ∈ Set.Icc ((49523 / 512000) : ℝ) (9911 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((242685553 / 200000000) : ℝ) ≤ Real.exp (2 * (49523 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49523 / 512000)) (242685553 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9911 / 102400) : ℝ)) ≤ (606789727 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9911 / 102400)) (606789727 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((18518224441 / 200000) : ℝ) ≤ Real.exp (3 * (3811983 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3811983 / 1000000)) (18518224441 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((49523 / 512000) : ℝ) (9911 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3811983 / 1000000) (1906291 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (49523 / 512000) (9911 / 102400) (242685553 / 200000000) (606789727 / 500000000) (3811983 / 1000000) (1906291 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (49523 / 512000) (9911 / 102400) (3811983 / 1000000) (1906291 / 500000) (35249 / 1000) (4409 / 125)
    (8031 / 125) (16151 / 250) (-567909 / 1000) (12307 / 40000) (422578 / 125) (691211 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3811983 / 1000000) (18518224441 / 200000) (691211 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3811983 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3811983 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell964 :
    ∀ t ∈ Set.Icc ((9911 / 102400) : ℝ) (49587 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1213579453 / 1000000000) : ℝ) ≤ Real.exp (2 * (9911 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9911 / 102400)) (1213579453 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((49587 / 512000) : ℝ)) ≤ (1213731161 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49587 / 512000)) (1213731161 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((46361718333 / 500000) : ℝ) ≤ Real.exp (3 * (3812459 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3812459 / 1000000)) (46361718333 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9911 / 102400) : ℝ) (49587 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3812459 / 1000000) (1906529 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9911 / 102400) (49587 / 512000) (1213579453 / 1000000000) (1213731161 / 1000000000) (3812459 / 1000000) (1906529 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9911 / 102400) (49587 / 512000) (3812459 / 1000000) (1906529 / 500000) (35261 / 1000) (35283 / 1000)
    (8039 / 125) (16167 / 250) (-141991 / 250) (307351 / 1000000) (422789 / 125) (2760899 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3812459 / 1000000) (46361718333 / 500000) (2760899 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3812459 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3812459 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell965 :
    ∀ t ∈ Set.Icc ((49587 / 512000) : ℝ) (49619 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((30343279 / 25000000) : ℝ) ≤ Real.exp (2 * (49587 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49587 / 512000)) (30343279 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((49619 / 512000) : ℝ)) ≤ (1213882887 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49619 / 512000)) (1213882887 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3714248751 / 40000) : ℝ) ≤ Real.exp (3 * (476617 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (476617 / 125000)) (3714248751 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((49587 / 512000) : ℝ) (49619 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (476617 / 125000) (762707 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (49587 / 512000) (49619 / 512000) (30343279 / 25000000) (1213882887 / 1000000000) (476617 / 125000) (762707 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (49587 / 512000) (49619 / 512000) (476617 / 125000) (762707 / 200000) (4409 / 125) (7059 / 200)
    (8047 / 125) (64733 / 1000) (-284009 / 500) (307027 / 1000000) (676801 / 200) (2756951 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (476617 / 125000) (3714248751 / 40000) (2756951 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (476617 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (476617 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell966 :
    ∀ t ∈ Set.Icc ((49619 / 512000) : ℝ) (49651 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((606941443 / 500000000) : ℝ) ≤ Real.exp (2 * (49619 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49619 / 512000)) (606941443 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((49651 / 512000) : ℝ)) ≤ (151754329 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49651 / 512000)) (151754329 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((9298919103 / 100000) : ℝ) ≤ Real.exp (3 * (3813413 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3813413 / 1000000)) (9298919103 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((49619 / 512000) : ℝ) (49651 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3813413 / 1000000) (953503 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (49619 / 512000) (49651 / 512000) (606941443 / 500000000) (151754329 / 125000000) (3813413 / 1000000) (953503 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (49619 / 512000) (49651 / 512000) (3813413 / 1000000) (953503 / 250000) (8821 / 250) (35307 / 1000)
    (64441 / 1000) (64797 / 1000) (-568073 / 1000) (306703 / 1000000) (1692849 / 500) (2753009 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3813413 / 1000000) (9298919103 / 100000) (2753009 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3813413 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3813413 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell967 :
    ∀ t ∈ Set.Icc ((49651 / 512000) : ℝ) (49683 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1214034631 / 1000000000) : ℝ) ≤ Real.exp (2 * (49651 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49651 / 512000)) (1214034631 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((49683 / 512000) : ℝ)) ≤ (303546599 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49683 / 512000)) (303546599 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((46561037169 / 500000) : ℝ) ≤ Real.exp (3 * (3813889 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3813889 / 1000000)) (46561037169 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((49651 / 512000) : ℝ) (49683 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3813889 / 1000000) (476811 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (49651 / 512000) (49683 / 512000) (1214034631 / 1000000000) (303546599 / 250000000) (3813889 / 1000000) (476811 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (49651 / 512000) (49683 / 512000) (3813889 / 1000000) (476811 / 125000) (4412 / 125) (17659 / 500)
    (12901 / 200) (64861 / 1000) (-568127 / 1000) (15319 / 50000) (3387389 / 1000) (68727 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3813889 / 1000000) (46561037169 / 500000) (68727 / 25000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3813889 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3813889 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell968 :
    ∀ t ∈ Set.Icc ((49683 / 512000) : ℝ) (9943 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((242837279 / 200000000) : ℝ) ≤ Real.exp (2 * (49683 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49683 / 512000)) (242837279 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9943 / 102400) : ℝ)) ≤ (607169089 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9943 / 102400)) (607169089 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((18651085461 / 200000) : ℝ) ≤ Real.exp (3 * (1907183 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1907183 / 500000)) (18651085461 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((49683 / 512000) : ℝ) (9943 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1907183 / 500000) (762993 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (49683 / 512000) (9943 / 102400) (242837279 / 200000000) (607169089 / 500000000) (1907183 / 500000) (762993 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (49683 / 512000) (9943 / 102400) (1907183 / 500000) (762993 / 200000) (35307 / 1000) (3533 / 100)
    (6457 / 100) (32463 / 500) (-568181 / 1000) (306057 / 1000000) (847271 / 250) (2745149 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1907183 / 500000) (18651085461 / 200000) (2745149 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1907183 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1907183 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell969 :
    ∀ t ∈ Set.Icc ((9943 / 102400) : ℝ) (49747 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1214338177 / 1000000000) : ℝ) ≤ Real.exp (2 * (9943 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9943 / 102400)) (1214338177 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((49747 / 512000) : ℝ)) ≤ (60724499 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49747 / 512000)) (60724499 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((18677794247 / 200000) : ℝ) ≤ Real.exp (3 * (3814843 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3814843 / 1000000)) (18677794247 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9943 / 102400) : ℝ) (49747 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3814843 / 1000000) (1907721 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9943 / 102400) (49747 / 512000) (1214338177 / 1000000000) (60724499 / 50000000) (3814843 / 1000000) (1907721 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9943 / 102400) (49747 / 512000) (3814843 / 1000000) (1907721 / 500000) (35319 / 1000) (17671 / 500)
    (32317 / 500) (64991 / 1000) (-142059 / 250) (152867 / 500000) (3390779 / 1000) (342653 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3814843 / 1000000) (18677794247 / 200000) (342653 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3814843 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3814843 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell970 :
    ∀ t ∈ Set.Icc ((49747 / 512000) : ℝ) (49779 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1214489979 / 1000000000) : ℝ) ≤ Real.exp (2 * (49747 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49747 / 512000)) (1214489979 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((49779 / 512000) : ℝ)) ≤ (1214641801 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49779 / 512000)) (1214641801 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((93522706403 / 1000000) : ℝ) ≤ Real.exp (3 * (95383 / 25000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (95383 / 25000)) (93522706403 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((49747 / 512000) : ℝ) (49779 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (95383 / 25000) (3815919 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (49747 / 512000) (49779 / 512000) (1214489979 / 1000000000) (1214641801 / 1000000000) (95383 / 25000) (3815919 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (49747 / 512000) (49779 / 512000) (95383 / 25000) (3815919 / 1000000) (35331 / 1000) (17677 / 500)
    (64699 / 1000) (13011 / 200) (-56829 / 100) (305411 / 1000000) (135699 / 40) (342163 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (95383 / 25000) (93522706403 / 1000000) (342163 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (95383 / 25000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (95383 / 25000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell971 :
    ∀ t ∈ Set.Icc ((49779 / 512000) : ℝ) (49811 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((6073209 / 5000000) : ℝ) ≤ Real.exp (2 * (49779 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49779 / 512000)) (6073209 / 5000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((49811 / 512000) : ℝ)) ≤ (1214793641 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49811 / 512000)) (1214793641 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((93656633083 / 1000000) : ℝ) ≤ Real.exp (3 * (3815797 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3815797 / 1000000)) (93656633083 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((49779 / 512000) : ℝ) (49811 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3815797 / 1000000) (954099 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (49779 / 512000) (49811 / 512000) (6073209 / 5000000) (1214793641 / 1000000000) (3815797 / 1000000) (954099 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (49779 / 512000) (49811 / 512000) (3815797 / 1000000) (954099 / 250000) (17671 / 500) (7073 / 200)
    (16191 / 250) (1628 / 25) (-71043 / 125) (305089 / 1000000) (3394171 / 1000) (2733389 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3815797 / 1000000) (93656633083 / 1000000) (2733389 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3815797 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3815797 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell972 :
    ∀ t ∈ Set.Icc ((49811 / 512000) : ℝ) (49843 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((30369841 / 25000000) : ℝ) ≤ Real.exp (2 * (49811 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49811 / 512000)) (30369841 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((49843 / 512000) : ℝ)) ≤ (1214945499 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49843 / 512000)) (1214945499 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((93790751549 / 1000000) : ℝ) ≤ Real.exp (3 * (1908137 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1908137 / 500000)) (93790751549 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((49811 / 512000) : ℝ) (49843 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1908137 / 500000) (3816873 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (49811 / 512000) (49843 / 512000) (30369841 / 25000000) (1214945499 / 1000000000) (1908137 / 500000) (3816873 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (49811 / 512000) (49843 / 512000) (1908137 / 500000) (3816873 / 1000000) (17677 / 500) (35377 / 1000)
    (16207 / 250) (13037 / 200) (-568397 / 1000) (304767 / 1000000) (3395869 / 1000) (2729481 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1908137 / 500000) (93790751549 / 1000000) (2729481 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1908137 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1908137 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell973 :
    ∀ t ∈ Set.Icc ((49843 / 512000) : ℝ) (399 / 4096), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((607472749 / 500000000) : ℝ) ≤ Real.exp (2 * (49843 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49843 / 512000)) (607472749 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((399 / 4096) : ℝ)) ≤ (1215097377 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (399 / 4096)) (1215097377 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3757002483 / 40000) : ℝ) ≤ Real.exp (3 * (3816751 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3816751 / 1000000)) (3757002483 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((49843 / 512000) : ℝ) (399 / 4096),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3816751 / 1000000) (76347 / 20000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (49843 / 512000) (399 / 4096) (607472749 / 500000000) (1215097377 / 1000000000) (3816751 / 1000000) (76347 / 20000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (49843 / 512000) (399 / 4096) (3816751 / 1000000) (76347 / 20000) (17683 / 500) (35389 / 1000)
    (64893 / 1000) (65249 / 1000) (-568451 / 1000) (60889 / 200000) (3397567 / 1000) (1362789 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3816751 / 1000000) (3757002483 / 40000) (1362789 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3816751 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3816751 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell974 :
    ∀ t ∈ Set.Icc ((399 / 4096) : ℝ) (49907 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((37971793 / 31250000) : ℝ) ≤ Real.exp (2 * (399 / 4096)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (399 / 4096)) (37971793 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((49907 / 512000) : ℝ)) ≤ (607624637 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49907 / 512000)) (607624637 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((94059564937 / 1000000) : ℝ) ≤ Real.exp (3 * (954307 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (954307 / 250000)) (94059564937 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((399 / 4096) : ℝ) (49907 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (954307 / 250000) (954457 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (399 / 4096) (49907 / 512000) (37971793 / 31250000) (607624637 / 500000000) (954307 / 250000) (954457 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (399 / 4096) (49907 / 512000) (954307 / 250000) (954457 / 250000) (35377 / 1000) (177 / 5)
    (64957 / 1000) (13063 / 200) (-1137 / 2) (76031 / 250000) (3399269 / 1000) (34021 / 12500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (954307 / 250000) (94059564937 / 1000000) (34021 / 12500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (954307 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (954307 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell975 :
    ∀ t ∈ Set.Icc ((49907 / 512000) : ℝ) (49939 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1215249273 / 1000000000) : ℝ) ≤ Real.exp (2 * (49907 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49907 / 512000)) (1215249273 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((49939 / 512000) : ℝ)) ≤ (1215401189 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49939 / 512000)) (1215401189 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((94194260409 / 1000000) : ℝ) ≤ Real.exp (3 * (763541 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (763541 / 200000)) (94194260409 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((49907 / 512000) : ℝ) (49939 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (763541 / 200000) (763661 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (49907 / 512000) (49939 / 512000) (1215249273 / 1000000000) (1215401189 / 1000000000) (763541 / 200000) (763661 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (49907 / 512000) (49939 / 512000) (763541 / 200000) (763661 / 200000) (35389 / 1000) (8853 / 250)
    (32511 / 500) (65379 / 1000) (-568553 / 1000) (303803 / 1000000) (425121 / 125) (679447 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (763541 / 200000) (94194260409 / 1000000) (679447 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (763541 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (763541 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell976 :
    ∀ t ∈ Set.Icc ((49939 / 512000) : ℝ) (49971 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((303850297 / 250000000) : ℝ) ≤ Real.exp (2 * (49939 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49939 / 512000)) (303850297 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((49971 / 512000) : ℝ)) ≤ (303888281 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49971 / 512000)) (303888281 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2947785899 / 31250) : ℝ) ≤ Real.exp (3 * (1909091 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1909091 / 500000)) (2947785899 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((49939 / 512000) : ℝ) (49971 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1909091 / 500000) (1909391 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (49939 / 512000) (49971 / 512000) (303850297 / 250000000) (303888281 / 250000000) (1909091 / 500000) (1909391 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (49939 / 512000) (49971 / 512000) (1909091 / 500000) (1909391 / 500000) (35401 / 1000) (4428 / 125)
    (65087 / 1000) (16361 / 250) (-284303 / 500) (151741 / 500000) (850667 / 250) (1356951 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1909091 / 500000) (2947785899 / 31250) (1356951 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1909091 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1909091 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell977 :
    ∀ t ∈ Set.Icc ((49971 / 512000) : ℝ) (50003 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1215553123 / 1000000000) : ℝ) ≤ Real.exp (2 * (49971 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49971 / 512000)) (1215553123 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((50003 / 512000) : ℝ)) ≤ (1215705077 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (50003 / 512000)) (1215705077 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((94464513683 / 1000000) : ℝ) ≤ Real.exp (3 * (190933 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (190933 / 50000)) (94464513683 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((49971 / 512000) : ℝ) (50003 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (190933 / 50000) (190963 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (49971 / 512000) (50003 / 512000) (1215553123 / 1000000000) (1215705077 / 1000000000) (190933 / 50000) (190963 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (49971 / 512000) (50003 / 512000) (190933 / 50000) (190963 / 50000) (35413 / 1000) (8859 / 250)
    (8144 / 125) (65509 / 1000) (-28433 / 50) (303161 / 1000000) (3404371 / 1000) (2710013 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (190933 / 50000) (94464513683 / 1000000) (2710013 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (190933 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (190933 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell978 :
    ∀ t ∈ Set.Icc ((50003 / 512000) : ℝ) (10007 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((303926269 / 250000000) : ℝ) ≤ Real.exp (2 * (50003 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (50003 / 512000)) (303926269 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((10007 / 102400) : ℝ)) ≤ (24317141 / 20000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (10007 / 102400)) (24317141 / 20000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((94599789051 / 1000000) : ℝ) ≤ Real.exp (3 * (3819137 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3819137 / 1000000)) (94599789051 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((50003 / 512000) : ℝ) (10007 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3819137 / 1000000) (3819737 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (50003 / 512000) (10007 / 102400) (303926269 / 250000000) (24317141 / 20000000) (3819137 / 1000000) (3819737 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (50003 / 512000) (10007 / 102400) (3819137 / 1000000) (3819737 / 1000000) (4428 / 125) (35447 / 1000)
    (8152 / 125) (32787 / 500) (-568713 / 1000) (302841 / 1000000) (3406073 / 1000) (1353069 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3819137 / 1000000) (94599789051 / 1000000) (1353069 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3819137 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3819137 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell979 :
    ∀ t ∈ Set.Icc ((10007 / 102400) : ℝ) (50067 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1215857049 / 1000000000) : ℝ) ≤ Real.exp (2 * (10007 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (10007 / 102400)) (1215857049 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((50067 / 512000) : ℝ)) ≤ (608004521 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (50067 / 512000)) (608004521 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((11841907267 / 125000) : ℝ) ≤ Real.exp (3 * (1909807 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1909807 / 500000)) (11841907267 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((10007 / 102400) : ℝ) (50067 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1909807 / 500000) (764043 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (10007 / 102400) (50067 / 512000) (1215857049 / 1000000000) (608004521 / 500000000) (1909807 / 500000) (764043 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (10007 / 102400) (50067 / 512000) (1909807 / 500000) (764043 / 200000) (8859 / 250) (35459 / 1000)
    (65281 / 1000) (65639 / 1000) (-568761 / 1000) (151261 / 500000) (1703889 / 500) (675567 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1909807 / 500000) (11841907267 / 125000) (675567 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1909807 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1909807 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch048 :
    ∀ t ∈ Set.Icc ((49427 / 512000) : ℝ) (50067 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell960
      hpThetaDensityLowerExpCompact_cell961)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell962
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell963
      hpThetaDensityLowerExpCompact_cell964)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell965
      hpThetaDensityLowerExpCompact_cell966)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell967
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell968
      hpThetaDensityLowerExpCompact_cell969))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell970
      hpThetaDensityLowerExpCompact_cell971)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell972
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell973
      hpThetaDensityLowerExpCompact_cell974)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell975
      hpThetaDensityLowerExpCompact_cell976)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell977
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell978
      hpThetaDensityLowerExpCompact_cell979)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch048
end HodgeProofHP
