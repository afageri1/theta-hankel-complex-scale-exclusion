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
theorem hpThetaDensityLowerExpCompact_cell660 :
    ∀ t ∈ Set.Icc ((43363 / 512000) : ℝ) (43371 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((296144537 / 250000000) : ℝ) ≤ Real.exp (2 * (43363 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43363 / 512000)) (296144537 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43371 / 512000) : ℝ)) ≤ (4627403 / 3906250) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43371 / 512000)) (4627403 / 3906250) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((70548502143 / 1000000) : ℝ) ≤ Real.exp (3 * (465169 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (465169 / 125000)) (70548502143 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43363 / 512000) : ℝ) (43371 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (465169 / 125000) (930397 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43363 / 512000) (43371 / 512000) (296144537 / 250000000) (4627403 / 3906250) (465169 / 125000) (930397 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43363 / 512000) (43371 / 512000) (465169 / 125000) (930397 / 250000) (4133 / 125) (33073 / 1000)
    (52593 / 1000) (52729 / 1000) (-69616 / 125) (375579 / 1000000) (3069257 / 1000) (362871 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (465169 / 125000) (70548502143 / 1000000) (362871 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (465169 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (465169 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell661 :
    ∀ t ∈ Set.Icc ((43371 / 512000) : ℝ) (43379 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1184615167 / 1000000000) : ℝ) ≤ Real.exp (2 * (43371 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43371 / 512000)) (1184615167 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43379 / 512000) : ℝ)) ≤ (296163047 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43379 / 512000)) (296163047 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((70573057281 / 1000000) : ℝ) ≤ Real.exp (3 * (930367 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (930367 / 250000)) (70573057281 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43371 / 512000) : ℝ) (43379 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (930367 / 250000) (465213 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43371 / 512000) (43379 / 512000) (1184615167 / 1000000000) (296163047 / 250000000) (930367 / 250000) (465213 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43371 / 512000) (43379 / 512000) (930367 / 250000) (465213 / 125000) (33067 / 1000) (8269 / 250)
    (6576 / 125) (52743 / 1000) (-556947 / 1000) (375483 / 1000000) (3069639 / 1000) (3627447 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (930367 / 250000) (70573057281 / 1000000) (3627447 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (930367 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (930367 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell662 :
    ∀ t ∈ Set.Icc ((43379 / 512000) : ℝ) (43387 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1184652187 / 1000000000) : ℝ) ≤ Real.exp (2 * (43379 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43379 / 512000)) (1184652187 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43387 / 512000) : ℝ)) ≤ (1184689209 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43387 / 512000)) (1184689209 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((35298810483 / 500000) : ℝ) ≤ Real.exp (3 * (232599 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (232599 / 62500)) (35298810483 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43379 / 512000) : ℝ) (43387 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (232599 / 62500) (186091 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43379 / 512000) (43387 / 512000) (1184652187 / 1000000000) (1184689209 / 1000000000) (232599 / 62500) (186091 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43379 / 512000) (43387 / 512000) (232599 / 62500) (186091 / 50000) (33069 / 1000) (33079 / 1000)
    (26311 / 500) (26379 / 500) (-278483 / 500) (93847 / 250000) (1535011 / 500) (725237 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (232599 / 62500) (35298810483 / 500000) (725237 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (232599 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (232599 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell663 :
    ∀ t ∈ Set.Icc ((43387 / 512000) : ℝ) (8679 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((148086151 / 125000000) : ℝ) ≤ Real.exp (2 * (43387 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43387 / 512000)) (148086151 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8679 / 102400) : ℝ)) ≤ (1184726231 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8679 / 102400)) (1184726231 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((70622405067 / 1000000) : ℝ) ≤ Real.exp (3 * (3721701 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3721701 / 1000000)) (70622405067 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43387 / 512000) : ℝ) (8679 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3721701 / 1000000) (232621 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43387 / 512000) (8679 / 102400) (148086151 / 125000000) (1184726231 / 1000000000) (3721701 / 1000000) (232621 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43387 / 512000) (8679 / 102400) (3721701 / 1000000) (232621 / 62500) (4134 / 125) (16541 / 500)
    (52637 / 1000) (13193 / 250) (-556989 / 1000) (375291 / 1000000) (614081 / 200) (226557 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3721701 / 1000000) (70622405067 / 1000000) (226557 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3721701 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3721701 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell664 :
    ∀ t ∈ Set.Icc ((8679 / 102400) : ℝ) (43403 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((118472623 / 100000000) : ℝ) ≤ Real.exp (2 * (8679 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8679 / 102400)) (118472623 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43403 / 512000) : ℝ)) ≤ (592381627 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43403 / 512000)) (592381627 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8830873241 / 125000) : ℝ) ≤ Real.exp (3 * (3721817 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3721817 / 1000000)) (8830873241 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8679 / 102400) : ℝ) (43403 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3721817 / 1000000) (3722053 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8679 / 102400) (43403 / 512000) (118472623 / 100000000) (592381627 / 500000000) (3721817 / 1000000) (3722053 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8679 / 102400) (43403 / 512000) (3721817 / 1000000) (3722053 / 1000000) (1323 / 40) (8271 / 250)
    (52651 / 1000) (52787 / 1000) (-139251 / 250) (93799 / 250000) (3070791 / 1000) (3623651 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3721817 / 1000000) (8830873241 / 125000) (3623651 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3721817 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3721817 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell665 :
    ∀ t ∈ Set.Icc ((43403 / 512000) : ℝ) (43411 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1184763253 / 1000000000) : ℝ) ≤ Real.exp (2 * (43403 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43403 / 512000)) (1184763253 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43411 / 512000) : ℝ)) ≤ (1184800279 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43411 / 512000)) (1184800279 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((14134315069 / 200000) : ℝ) ≤ Real.exp (3 * (3721933 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3721933 / 1000000)) (14134315069 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43403 / 512000) : ℝ) (43411 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3721933 / 1000000) (3722169 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43403 / 512000) (43411 / 512000) (1184763253 / 1000000000) (1184800279 / 1000000000) (3721933 / 1000000) (3722169 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43403 / 512000) (43411 / 512000) (3721933 / 1000000) (3722169 / 1000000) (16539 / 500) (33087 / 1000)
    (10533 / 200) (52801 / 1000) (-557023 / 1000) (375101 / 1000000) (1535587 / 500) (362239 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3721933 / 1000000) (14134315069 / 200000) (362239 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3721933 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3721933 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell666 :
    ∀ t ∈ Set.Icc ((43411 / 512000) : ℝ) (43419 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((592400139 / 500000000) : ℝ) ≤ Real.exp (2 * (43411 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43411 / 512000)) (592400139 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43419 / 512000) : ℝ)) ≤ (148104663 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43419 / 512000)) (148104663 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((70696385409 / 1000000) : ℝ) ≤ Real.exp (3 * (74441 / 20000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (74441 / 20000)) (70696385409 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43411 / 512000) : ℝ) (43419 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (74441 / 20000) (744457 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43411 / 512000) (43419 / 512000) (592400139 / 500000000) (148104663 / 125000000) (74441 / 20000) (744457 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43411 / 512000) (43419 / 512000) (74441 / 20000) (744457 / 200000) (827 / 25) (3309 / 100)
    (1317 / 25) (10563 / 200) (-278523 / 500) (93751 / 250000) (3071557 / 1000) (3621119 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (74441 / 20000) (70696385409 / 1000000) (3621119 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (74441 / 20000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (74441 / 20000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell667 :
    ∀ t ∈ Set.Icc ((43419 / 512000) : ℝ) (43427 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1184837303 / 1000000000) : ℝ) ≤ Real.exp (2 * (43419 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43419 / 512000)) (1184837303 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43427 / 512000) : ℝ)) ≤ (1184874331 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43427 / 512000)) (1184874331 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((70720992019 / 1000000) : ℝ) ≤ Real.exp (3 * (1861083 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1861083 / 500000)) (70720992019 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43419 / 512000) : ℝ) (43427 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1861083 / 500000) (1861201 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43419 / 512000) (43427 / 512000) (1184837303 / 1000000000) (1184874331 / 1000000000) (1861083 / 500000) (1861201 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43419 / 512000) (43427 / 512000) (1861083 / 500000) (1861201 / 500000) (33083 / 1000) (33093 / 1000)
    (26347 / 500) (5283 / 100) (-557061 / 1000) (374909 / 1000000) (3071943 / 1000) (3619859 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1861083 / 500000) (70720992019 / 1000000) (3619859 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1861083 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1861083 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell668 :
    ∀ t ∈ Set.Icc ((43427 / 512000) : ℝ) (8687 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((118487433 / 100000000) : ℝ) ≤ Real.exp (2 * (43427 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43427 / 512000)) (118487433 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8687 / 102400) : ℝ)) ≤ (1184911359 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8687 / 102400)) (1184911359 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((35372803597 / 500000) : ℝ) ≤ Real.exp (3 * (1861141 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1861141 / 500000)) (35372803597 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43427 / 512000) : ℝ) (8687 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1861141 / 500000) (1861259 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43427 / 512000) (8687 / 102400) (118487433 / 100000000) (1184911359 / 1000000000) (1861141 / 500000) (1861259 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43427 / 512000) (8687 / 102400) (1861141 / 500000) (1861259 / 500000) (16543 / 500) (6619 / 200)
    (52709 / 1000) (13211 / 250) (-13927 / 25) (187407 / 500000) (1536163 / 500) (18093 / 5000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1861141 / 500000) (35372803597 / 500000) (18093 / 5000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1861141 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1861141 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell669 :
    ∀ t ∈ Set.Icc ((8687 / 102400) : ℝ) (43443 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((592455679 / 500000000) : ℝ) ≤ Real.exp (2 * (8687 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8687 / 102400)) (592455679 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43443 / 512000) : ℝ)) ≤ (296237097 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43443 / 512000)) (296237097 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4423152703 / 62500) : ℝ) ≤ Real.exp (3 * (3722399 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3722399 / 1000000)) (4423152703 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8687 / 102400) : ℝ) (43443 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3722399 / 1000000) (1861317 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8687 / 102400) (43443 / 512000) (592455679 / 500000000) (296237097 / 250000000) (3722399 / 1000000) (1861317 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8687 / 102400) (43443 / 512000) (3722399 / 1000000) (1861317 / 500000) (33089 / 1000) (16549 / 500)
    (52723 / 1000) (52859 / 1000) (-557103 / 1000) (374717 / 1000000) (3072709 / 1000) (361733 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3722399 / 1000000) (4423152703 / 62500) (361733 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3722399 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3722399 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell670 :
    ∀ t ∈ Set.Icc ((43443 / 512000) : ℝ) (43451 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1184948387 / 1000000000) : ℝ) ≤ Real.exp (2 * (43443 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43443 / 512000)) (1184948387 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43451 / 512000) : ℝ)) ≤ (592492709 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43451 / 512000)) (592492709 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((14159015127 / 200000) : ℝ) ≤ Real.exp (3 * (744503 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (744503 / 200000)) (14159015127 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43443 / 512000) : ℝ) (43451 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (744503 / 200000) (3722751 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43443 / 512000) (43451 / 512000) (1184948387 / 1000000000) (592492709 / 500000000) (744503 / 200000) (3722751 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43443 / 512000) (43451 / 512000) (744503 / 200000) (3722751 / 1000000) (33091 / 1000) (33101 / 1000)
    (26369 / 500) (52873 / 1000) (-278559 / 500) (187311 / 500000) (614619 / 200) (3616071 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (744503 / 200000) (14159015127 / 200000) (3616071 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (744503 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (744503 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell671 :
    ∀ t ∈ Set.Icc ((43451 / 512000) : ℝ) (43459 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1184985417 / 1000000000) : ℝ) ≤ Real.exp (2 * (43451 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43451 / 512000)) (1184985417 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43459 / 512000) : ℝ)) ≤ (23700449 / 20000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43459 / 512000)) (23700449 / 20000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((14163943319 / 200000) : ℝ) ≤ Real.exp (3 * (3722631 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3722631 / 1000000)) (14163943319 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43451 / 512000) : ℝ) (43459 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3722631 / 1000000) (3722867 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43451 / 512000) (43459 / 512000) (1184985417 / 1000000000) (23700449 / 20000000) (3722631 / 1000000) (3722867 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43451 / 512000) (43459 / 512000) (3722631 / 1000000) (3722867 / 1000000) (16547 / 500) (4138 / 125)
    (6594 / 125) (6611 / 125) (-557137 / 1000) (374527 / 1000000) (1536739 / 500) (3614813 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3722631 / 1000000) (14163943319 / 200000) (3614813 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3722631 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3722631 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell672 :
    ∀ t ∈ Set.Icc ((43459 / 512000) : ℝ) (43467 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1185022449 / 1000000000) : ℝ) ≤ Real.exp (2 * (43459 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43459 / 512000)) (1185022449 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43467 / 512000) : ℝ)) ≤ (592529741 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43467 / 512000)) (592529741 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((35422289333 / 500000) : ℝ) ≤ Real.exp (3 * (930687 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (930687 / 250000)) (35422289333 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43459 / 512000) : ℝ) (43467 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (930687 / 250000) (3722983 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43459 / 512000) (43467 / 512000) (1185022449 / 1000000000) (592529741 / 500000000) (930687 / 250000) (3722983 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43459 / 512000) (43467 / 512000) (930687 / 250000) (3722983 / 1000000) (33097 / 1000) (16553 / 500)
    (52767 / 1000) (26451 / 500) (-13929 / 25) (37443 / 100000) (3073861 / 1000) (451693 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (930687 / 250000) (35422289333 / 500000) (451693 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (930687 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (930687 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell673 :
    ∀ t ∈ Set.Icc ((43467 / 512000) : ℝ) (1739 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1185059481 / 1000000000) : ℝ) ≤ Real.exp (2 * (43467 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43467 / 512000)) (1185059481 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1739 / 20480) : ℝ)) ≤ (296274129 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1739 / 20480)) (296274129 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8858654607 / 125000) : ℝ) ≤ Real.exp (3 * (232679 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (232679 / 62500)) (8858654607 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43467 / 512000) : ℝ) (1739 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (232679 / 62500) (37231 / 10000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43467 / 512000) (1739 / 20480) (1185059481 / 1000000000) (296274129 / 250000000) (232679 / 62500) (37231 / 10000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43467 / 512000) (1739 / 20480) (232679 / 62500) (37231 / 10000) (331 / 10) (33109 / 1000)
    (52781 / 1000) (52917 / 1000) (-22287 / 40) (74867 / 200000) (384281 / 125) (3612287 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (232679 / 62500) (8858654607 / 125000) (3612287 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (232679 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (232679 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell674 :
    ∀ t ∈ Set.Icc ((1739 / 20480) : ℝ) (43483 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((237019303 / 200000000) : ℝ) ≤ Real.exp (2 * (1739 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1739 / 20480)) (237019303 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43483 / 512000) : ℝ)) ≤ (1185133551 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43483 / 512000)) (1185133551 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((7089390363 / 100000) : ℝ) ≤ Real.exp (3 * (186149 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (186149 / 50000)) (7089390363 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1739 / 20480) : ℝ) (43483 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (186149 / 50000) (232701 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1739 / 20480) (43483 / 512000) (237019303 / 200000000) (1185133551 / 1000000000) (186149 / 50000) (232701 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1739 / 20480) (43483 / 512000) (186149 / 50000) (232701 / 62500) (33103 / 1000) (4139 / 125)
    (10559 / 200) (52931 / 1000) (-557193 / 1000) (2339 / 6250) (3074631 / 1000) (361103 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (186149 / 50000) (7089390363 / 100000) (361103 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (186149 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (186149 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell675 :
    ∀ t ∈ Set.Icc ((43483 / 512000) : ℝ) (43491 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((23702671 / 20000000) : ℝ) ≤ Real.exp (2 * (43483 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43483 / 512000)) (23702671 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43491 / 512000) : ℝ)) ≤ (1185170587 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43491 / 512000)) (1185170587 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1108106121 / 15625) : ℝ) ≤ Real.exp (3 * (3723097 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3723097 / 1000000)) (1108106121 / 15625) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43483 / 512000) : ℝ) (43491 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3723097 / 1000000) (930833 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43483 / 512000) (43491 / 512000) (23702671 / 20000000) (1185170587 / 1000000000) (3723097 / 1000000) (930833 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43483 / 512000) (43491 / 512000) (3723097 / 1000000) (930833 / 250000) (6621 / 200) (6623 / 200)
    (5281 / 100) (10589 / 200) (-557217 / 1000) (5846 / 15625) (1537507 / 500) (3609763 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3723097 / 1000000) (1108106121 / 15625) (3609763 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3723097 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3723097 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell676 :
    ∀ t ∈ Set.Icc ((43491 / 512000) : ℝ) (43499 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((592585293 / 500000000) : ℝ) ≤ Real.exp (2 * (43491 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43491 / 512000)) (592585293 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43499 / 512000) : ℝ)) ≤ (148150953 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43499 / 512000)) (148150953 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((35471737883 / 500000) : ℝ) ≤ Real.exp (3 * (3723213 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3723213 / 1000000)) (35471737883 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43491 / 512000) : ℝ) (43499 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3723213 / 1000000) (3723449 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43491 / 512000) (43499 / 512000) (592585293 / 500000000) (148150953 / 125000000) (3723213 / 1000000) (3723449 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43491 / 512000) (43499 / 512000) (3723213 / 1000000) (3723449 / 1000000) (8277 / 250) (16559 / 500)
    (6603 / 125) (1324 / 25) (-557231 / 1000) (374049 / 1000000) (3075401 / 1000) (3608507 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3723213 / 1000000) (35471737883 / 500000) (3608507 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3723213 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3723213 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell677 :
    ∀ t ∈ Set.Icc ((43499 / 512000) : ℝ) (43507 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1185207623 / 1000000000) : ℝ) ≤ Real.exp (2 * (43499 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43499 / 512000)) (1185207623 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43507 / 512000) : ℝ)) ≤ (592622331 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43507 / 512000)) (592622331 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((35484084189 / 500000) : ℝ) ≤ Real.exp (3 * (3723329 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3723329 / 1000000)) (35484084189 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43499 / 512000) : ℝ) (43507 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3723329 / 1000000) (744713 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43499 / 512000) (43507 / 512000) (1185207623 / 1000000000) (592622331 / 500000000) (3723329 / 1000000) (744713 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43499 / 512000) (43507 / 512000) (3723329 / 1000000) (744713 / 200000) (33111 / 1000) (828 / 25)
    (52839 / 1000) (2119 / 40) (-2229 / 4) (373953 / 1000000) (384473 / 125) (901813 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3723329 / 1000000) (35484084189 / 500000) (901813 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3723329 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3723329 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell678 :
    ∀ t ∈ Set.Icc ((43507 / 512000) : ℝ) (8703 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1185244661 / 1000000000) : ℝ) ≤ Real.exp (2 * (43507 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43507 / 512000)) (1185244661 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8703 / 102400) : ℝ)) ≤ (592640851 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8703 / 102400)) (592640851 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((17748270641 / 250000) : ℝ) ≤ Real.exp (3 * (1861723 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1861723 / 500000)) (17748270641 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43507 / 512000) : ℝ) (8703 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1861723 / 500000) (3723681 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43507 / 512000) (8703 / 102400) (1185244661 / 1000000000) (592640851 / 500000000) (1861723 / 500000) (3723681 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43507 / 512000) (8703 / 102400) (1861723 / 500000) (3723681 / 1000000) (16557 / 500) (33123 / 1000)
    (26427 / 500) (52989 / 1000) (-278637 / 500) (373857 / 1000000) (3076167 / 1000) (1802993 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1861723 / 500000) (17748270641 / 250000) (1802993 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1861723 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1861723 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell679 :
    ∀ t ∈ Set.Icc ((8703 / 102400) : ℝ) (43523 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1185281701 / 1000000000) : ℝ) ≤ Real.exp (2 * (8703 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8703 / 102400)) (1185281701 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43523 / 512000) : ℝ)) ≤ (592659371 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43523 / 512000)) (592659371 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((71017792443 / 1000000) : ℝ) ≤ Real.exp (3 * (1861781 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1861781 / 500000)) (71017792443 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8703 / 102400) : ℝ) (43523 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1861781 / 500000) (1861899 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8703 / 102400) (43523 / 512000) (1185281701 / 1000000000) (592659371 / 500000000) (1861781 / 500000) (1861899 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8703 / 102400) (43523 / 512000) (1861781 / 500000) (1861899 / 500000) (8279 / 250) (16563 / 500)
    (13217 / 250) (13251 / 250) (-69661 / 125) (186881 / 500000) (1538277 / 500) (3604731 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1861781 / 500000) (71017792443 / 1000000) (3604731 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1861781 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1861781 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch033 :
    ∀ t ∈ Set.Icc ((43363 / 512000) : ℝ) (43523 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell660
      hpThetaDensityLowerExpCompact_cell661)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell662
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell663
      hpThetaDensityLowerExpCompact_cell664)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell665
      hpThetaDensityLowerExpCompact_cell666)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell667
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell668
      hpThetaDensityLowerExpCompact_cell669))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell670
      hpThetaDensityLowerExpCompact_cell671)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell672
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell673
      hpThetaDensityLowerExpCompact_cell674)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell675
      hpThetaDensityLowerExpCompact_cell676)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell677
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell678
      hpThetaDensityLowerExpCompact_cell679)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch033
end HodgeProofHP
