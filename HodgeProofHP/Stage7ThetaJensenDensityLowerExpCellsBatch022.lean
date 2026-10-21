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
theorem hpThetaDensityLowerExpCompact_cell440 :
    ∀ t ∈ Set.Icc ((41899 / 512000) : ℝ) (41903 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((147227897 / 125000000) : ℝ) ≤ Real.exp (2 * (41899 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41899 / 512000)) (147227897 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41903 / 512000) : ℝ)) ≤ (58892079 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41903 / 512000)) (58892079 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66197154487 / 1000000) : ℝ) ≤ Real.exp (3 * (3700131 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3700131 / 1000000)) (66197154487 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41899 / 512000) : ℝ) (41903 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3700131 / 1000000) (925077 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41899 / 512000) (41903 / 512000) (147227897 / 125000000) (58892079 / 50000000) (3700131 / 1000000) (925077 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41899 / 512000) (41903 / 512000) (3700131 / 1000000) (925077 / 250000) (16281 / 500) (32569 / 1000)
    (50) (50101 / 1000) (-553611 / 1000) (2459 / 6250) (2999657 / 1000) (966809 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3700131 / 1000000) (66197154487 / 1000000) (966809 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3700131 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3700131 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell441 :
    ∀ t ∈ Set.Icc ((41903 / 512000) : ℝ) (41907 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1177841579 / 1000000000) : ℝ) ≤ Real.exp (2 * (41903 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41903 / 512000)) (1177841579 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41907 / 512000) : ℝ)) ≤ (73616249 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41907 / 512000)) (73616249 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66208673789 / 1000000) : ℝ) ≤ Real.exp (3 * (3700189 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3700189 / 1000000)) (66208673789 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41903 / 512000) : ℝ) (41907 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3700189 / 1000000) (740073 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41903 / 512000) (41907 / 512000) (1177841579 / 1000000000) (73616249 / 62500000) (3700189 / 1000000) (740073 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41903 / 512000) (41907 / 512000) (3700189 / 1000000) (740073 / 200000) (32563 / 1000) (3257 / 100)
    (50007 / 1000) (12527 / 250) (-4429 / 8) (39339 / 100000) (1499921 / 500) (3866563 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3700189 / 1000000) (66208673789 / 1000000) (3866563 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3700189 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3700189 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell442 :
    ∀ t ∈ Set.Icc ((41907 / 512000) : ℝ) (41911 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1177859983 / 1000000000) : ℝ) ≤ Real.exp (2 * (41907 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41907 / 512000)) (1177859983 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41911 / 512000) : ℝ)) ≤ (294469597 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41911 / 512000)) (294469597 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13244039019 / 200000) : ℝ) ≤ Real.exp (3 * (3700247 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3700247 / 1000000)) (13244039019 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41907 / 512000) : ℝ) (41911 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3700247 / 1000000) (3700423 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41907 / 512000) (41911 / 512000) (1177859983 / 1000000000) (294469597 / 250000000) (3700247 / 1000000) (3700423 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41907 / 512000) (41911 / 512000) (3700247 / 1000000) (3700423 / 1000000) (8141 / 250) (8143 / 250)
    (25007 / 500) (10023 / 200) (-110727 / 200) (19667 / 50000) (300003 / 100) (3865891 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3700247 / 1000000) (13244039019 / 200000) (3865891 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3700247 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3700247 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell443 :
    ∀ t ∈ Set.Icc ((41911 / 512000) : ℝ) (8383 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1177878387 / 1000000000) : ℝ) ≤ Real.exp (2 * (41911 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41911 / 512000)) (1177878387 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8383 / 102400) : ℝ)) ≤ (1177896793 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8383 / 102400)) (1177896793 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66231519711 / 1000000) : ℝ) ≤ Real.exp (3 * (231269 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (231269 / 62500)) (66231519711 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41911 / 512000) : ℝ) (8383 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (231269 / 62500) (3700481 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41911 / 512000) (8383 / 102400) (1177878387 / 1000000000) (1177896793 / 1000000000) (231269 / 62500) (3700481 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41911 / 512000) (8383 / 102400) (231269 / 62500) (3700481 / 1000000) (16283 / 500) (32573 / 1000)
    (50021 / 1000) (25061 / 500) (-553641 / 1000) (393291 / 1000000) (1500109 / 500) (386523 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (231269 / 62500) (66231519711 / 1000000) (386523 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (231269 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (231269 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell444 :
    ∀ t ∈ Set.Icc ((8383 / 102400) : ℝ) (41919 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((147237099 / 125000000) : ℝ) ≤ Real.exp (2 * (8383 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8383 / 102400)) (147237099 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41919 / 512000) : ℝ)) ≤ (588957599 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41919 / 512000)) (588957599 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66243044993 / 1000000) : ℝ) ≤ Real.exp (3 * (1850181 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1850181 / 500000)) (66243044993 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8383 / 102400) : ℝ) (41919 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1850181 / 500000) (3700539 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8383 / 102400) (41919 / 512000) (147237099 / 125000000) (588957599 / 500000000) (1850181 / 500000) (3700539 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8383 / 102400) (41919 / 512000) (1850181 / 500000) (3700539 / 1000000) (32567 / 1000) (16287 / 500)
    (12507 / 250) (50129 / 1000) (-553651 / 1000) (393241 / 1000000) (1500203 / 500) (3864557 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1850181 / 500000) (66243044993 / 1000000) (3864557 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1850181 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1850181 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell445 :
    ∀ t ∈ Set.Icc ((41919 / 512000) : ℝ) (41923 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1177915197 / 1000000000) : ℝ) ≤ Real.exp (2 * (41919 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41919 / 512000)) (1177915197 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41923 / 512000) : ℝ)) ≤ (1177933603 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41923 / 512000)) (1177933603 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1656364307 / 25000) : ℝ) ≤ Real.exp (3 * (185021 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (185021 / 50000)) (1656364307 / 25000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41919 / 512000) : ℝ) (41923 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (185021 / 50000) (3700597 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41919 / 512000) (41923 / 512000) (1177915197 / 1000000000) (1177933603 / 1000000000) (185021 / 50000) (3700597 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41919 / 512000) (41923 / 512000) (185021 / 50000) (3700597 / 1000000) (4071 / 125) (4072 / 125)
    (10007 / 200) (6267 / 125) (-553661 / 1000) (393191 / 1000000) (1500297 / 500) (772777 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (185021 / 50000) (1656364307 / 25000) (772777 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (185021 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (185021 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell446 :
    ∀ t ∈ Set.Icc ((41923 / 512000) : ℝ) (41927 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((588966801 / 500000000) : ℝ) ≤ Real.exp (2 * (41923 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41923 / 512000)) (588966801 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41927 / 512000) : ℝ)) ≤ (147244001 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41927 / 512000)) (147244001 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66266101573 / 1000000) : ℝ) ≤ Real.exp (3 * (1850239 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1850239 / 500000)) (66266101573 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41923 / 512000) : ℝ) (41927 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1850239 / 500000) (740131 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41923 / 512000) (41927 / 512000) (588966801 / 500000000) (147244001 / 125000000) (1850239 / 500000) (740131 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41923 / 512000) (41927 / 512000) (1850239 / 500000) (740131 / 200000) (3257 / 100) (32577 / 1000)
    (25021 / 500) (50143 / 1000) (-553671 / 1000) (393141 / 1000000) (1500391 / 500) (3863213 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1850239 / 500000) (66266101573 / 1000000) (3863213 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1850239 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1850239 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell447 :
    ∀ t ∈ Set.Icc ((41927 / 512000) : ℝ) (41931 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1177952007 / 1000000000) : ℝ) ≤ Real.exp (2 * (41927 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41927 / 512000)) (1177952007 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41931 / 512000) : ℝ)) ≤ (588985207 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41931 / 512000)) (588985207 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66277632873 / 1000000) : ℝ) ≤ Real.exp (3 * (462567 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (462567 / 125000)) (66277632873 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41927 / 512000) : ℝ) (41931 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (462567 / 125000) (462589 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41927 / 512000) (41931 / 512000) (1177952007 / 1000000000) (588985207 / 500000000) (462567 / 125000) (462589 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41927 / 512000) (41931 / 512000) (462567 / 125000) (462589 / 125000) (32571 / 1000) (16289 / 500)
    (1001 / 20) (1003 / 20) (-276843 / 500) (393091 / 1000000) (3000967 / 1000) (193127 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (462567 / 125000) (66277632873 / 1000000) (193127 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (462567 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (462567 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell448 :
    ∀ t ∈ Set.Icc ((41931 / 512000) : ℝ) (8387 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1177970413 / 1000000000) : ℝ) ≤ Real.exp (2 * (41931 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41931 / 512000)) (1177970413 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8387 / 102400) : ℝ)) ≤ (58899441 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8387 / 102400)) (58899441 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66289166179 / 1000000) : ℝ) ≤ Real.exp (3 * (1850297 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1850297 / 500000)) (66289166179 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41931 / 512000) : ℝ) (8387 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1850297 / 500000) (370077 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41931 / 512000) (8387 / 102400) (1177970413 / 1000000000) (58899441 / 50000000) (1850297 / 500000) (370077 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41931 / 512000) (8387 / 102400) (1850297 / 500000) (370077 / 100000) (8143 / 250) (1629 / 50)
    (50057 / 1000) (50157 / 1000) (-69212 / 125) (393041 / 1000000) (600231 / 200) (965467 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1850297 / 500000) (66289166179 / 1000000) (965467 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1850297 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1850297 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell449 :
    ∀ t ∈ Set.Icc ((8387 / 102400) : ℝ) (41939 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1177988819 / 1000000000) : ℝ) ≤ Real.exp (2 * (8387 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8387 / 102400)) (1177988819 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41939 / 512000) : ℝ)) ≤ (589003613 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41939 / 512000)) (589003613 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6630050259 / 100000) : ℝ) ≤ Real.exp (3 * (3700651 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3700651 / 1000000)) (6630050259 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8387 / 102400) : ℝ) (41939 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3700651 / 1000000) (925207 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8387 / 102400) (41939 / 512000) (1177988819 / 1000000000) (589003613 / 500000000) (3700651 / 1000000) (925207 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8387 / 102400) (41939 / 512000) (3700651 / 1000000) (925207 / 250000) (16287 / 500) (32581 / 1000)
    (50063 / 1000) (12541 / 250) (-553701 / 1000) (12281 / 31250) (3001343 / 1000) (482651 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3700651 / 1000000) (6630050259 / 100000) (482651 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3700651 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3700651 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell450 :
    ∀ t ∈ Set.Icc ((41939 / 512000) : ℝ) (41943 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((47120289 / 40000000) : ℝ) ≤ Real.exp (2 * (41939 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41939 / 512000)) (47120289 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41943 / 512000) : ℝ)) ≤ (36813301 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41943 / 512000)) (36813301 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16578009969 / 250000) : ℝ) ≤ Real.exp (3 * (3700709 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3700709 / 1000000)) (16578009969 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41939 / 512000) : ℝ) (41943 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3700709 / 1000000) (1850443 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41939 / 512000) (41943 / 512000) (47120289 / 40000000) (36813301 / 31250000) (3700709 / 1000000) (1850443 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41939 / 512000) (41943 / 512000) (3700709 / 1000000) (1850443 / 500000) (1303 / 40) (16291 / 500)
    (5007 / 100) (12543 / 250) (-553711 / 1000) (196471 / 500000) (3001531 / 1000) (482567 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3700709 / 1000000) (16578009969 / 250000) (482567 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3700709 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3700709 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell451 :
    ∀ t ∈ Set.Icc ((41943 / 512000) : ℝ) (41947 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1178025631 / 1000000000) : ℝ) ≤ Real.exp (2 * (41943 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41943 / 512000)) (1178025631 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41947 / 512000) : ℝ)) ≤ (1178044039 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41947 / 512000)) (1178044039 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6632357917 / 100000) : ℝ) ≤ Real.exp (3 * (3700767 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3700767 / 1000000)) (6632357917 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41943 / 512000) : ℝ) (41947 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3700767 / 1000000) (231309 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41943 / 512000) (41947 / 512000) (1178025631 / 1000000000) (1178044039 / 1000000000) (3700767 / 1000000) (231309 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41943 / 512000) (41947 / 512000) (3700767 / 1000000) (231309 / 62500) (32577 / 1000) (4073 / 125)
    (50077 / 1000) (50179 / 1000) (-553721 / 1000) (392893 / 1000000) (75043 / 25) (771973 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3700767 / 1000000) (6632357917 / 100000) (771973 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3700767 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3700767 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell452 :
    ∀ t ∈ Set.Icc ((41947 / 512000) : ℝ) (41951 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((589022019 / 500000000) : ℝ) ≤ Real.exp (2 * (41947 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41947 / 512000)) (589022019 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41951 / 512000) : ℝ)) ≤ (589031223 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41951 / 512000)) (589031223 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66335120471 / 1000000) : ℝ) ≤ Real.exp (3 * (148033 / 40000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (148033 / 40000)) (66335120471 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41947 / 512000) : ℝ) (41951 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (148033 / 40000) (3701001 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41947 / 512000) (41951 / 512000) (589022019 / 500000000) (589031223 / 500000000) (148033 / 40000) (3701001 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41947 / 512000) (41951 / 512000) (148033 / 40000) (3701001 / 1000000) (16289 / 500) (6517 / 200)
    (10017 / 200) (10037 / 200) (-69217 / 125) (196421 / 500000) (375238 / 125) (3859193 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (148033 / 40000) (66335120471 / 1000000) (3859193 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (148033 / 40000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (148033 / 40000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell453 :
    ∀ t ∈ Set.Icc ((41951 / 512000) : ℝ) (8391 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235612489 / 200000000) : ℝ) ≤ Real.exp (2 * (41951 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41951 / 512000)) (235612489 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8391 / 102400) : ℝ)) ≤ (589040427 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8391 / 102400)) (589040427 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66346663781 / 1000000) : ℝ) ≤ Real.exp (3 * (3700883 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3700883 / 1000000)) (66346663781 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41951 / 512000) : ℝ) (8391 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3700883 / 1000000) (3701059 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41951 / 512000) (8391 / 102400) (235612489 / 200000000) (589040427 / 500000000) (3700883 / 1000000) (3701059 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41951 / 512000) (8391 / 102400) (3700883 / 1000000) (3701059 / 1000000) (32579 / 1000) (32587 / 1000)
    (12523 / 250) (6274 / 125) (-276873 / 500) (392793 / 1000000) (3002093 / 1000) (1929261 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3700883 / 1000000) (66346663781 / 1000000) (1929261 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3700883 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3700883 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell454 :
    ∀ t ∈ Set.Icc ((8391 / 102400) : ℝ) (41959 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1178080853 / 1000000000) : ℝ) ≤ Real.exp (2 * (8391 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8391 / 102400)) (1178080853 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41959 / 512000) : ℝ)) ≤ (1178099261 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41959 / 512000)) (1178099261 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2654320401 / 40000) : ℝ) ≤ Real.exp (3 * (185047 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (185047 / 50000)) (2654320401 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8391 / 102400) : ℝ) (41959 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (185047 / 50000) (3701117 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8391 / 102400) (41959 / 512000) (1178080853 / 1000000000) (1178099261 / 1000000000) (185047 / 50000) (3701117 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8391 / 102400) (41959 / 512000) (185047 / 50000) (3701117 / 1000000) (32581 / 1000) (8147 / 250)
    (50099 / 1000) (251 / 5) (-553751 / 1000) (49093 / 125000) (3002281 / 1000) (1928931 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (185047 / 50000) (2654320401 / 40000) (1928931 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (185047 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (185047 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell455 :
    ∀ t ∈ Set.Icc ((41959 / 512000) : ℝ) (41963 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((58904963 / 50000000) : ℝ) ≤ Real.exp (2 * (41959 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41959 / 512000)) (58904963 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41963 / 512000) : ℝ)) ≤ (1178117669 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41963 / 512000)) (1178117669 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((33184778659 / 500000) : ℝ) ≤ Real.exp (3 * (1850499 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1850499 / 500000)) (33184778659 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41959 / 512000) : ℝ) (41963 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1850499 / 500000) (148047 / 40000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41959 / 512000) (41963 / 512000) (58904963 / 50000000) (1178117669 / 1000000000) (1850499 / 500000) (148047 / 40000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41959 / 512000) (41963 / 512000) (1850499 / 500000) (148047 / 40000) (16291 / 500) (32589 / 1000)
    (25053 / 500) (50207 / 1000) (-553761 / 1000) (196347 / 500000) (3002469 / 1000) (3857191 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1850499 / 500000) (33184778659 / 500000) (3857191 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1850499 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1850499 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell456 :
    ∀ t ∈ Set.Icc ((41963 / 512000) : ℝ) (41967 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((294529417 / 250000000) : ℝ) ≤ Real.exp (2 * (41963 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41963 / 512000)) (294529417 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41967 / 512000) : ℝ)) ≤ (1178136077 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41967 / 512000)) (1178136077 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3319055331 / 50000) : ℝ) ≤ Real.exp (3 * (57829 / 15625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (57829 / 15625)) (3319055331 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41963 / 512000) : ℝ) (41967 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (57829 / 15625) (3701233 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41963 / 512000) (41967 / 512000) (294529417 / 250000000) (1178136077 / 1000000000) (57829 / 15625) (3701233 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41963 / 512000) (41967 / 512000) (57829 / 15625) (3701233 / 1000000) (32583 / 1000) (32591 / 1000)
    (50113 / 1000) (25107 / 500) (-553771 / 1000) (98161 / 250000) (3002657 / 1000) (96413 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (57829 / 15625) (3319055331 / 50000) (96413 / 25000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (57829 / 15625)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (57829 / 15625)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell457 :
    ∀ t ∈ Set.Icc ((41967 / 512000) : ℝ) (41971 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((294534019 / 250000000) : ℝ) ≤ Real.exp (2 * (41967 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41967 / 512000)) (294534019 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41971 / 512000) : ℝ)) ≤ (589077243 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41971 / 512000)) (589077243 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16598164483 / 250000) : ℝ) ≤ Real.exp (3 * (1850557 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1850557 / 500000)) (16598164483 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41967 / 512000) : ℝ) (41971 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1850557 / 500000) (3701291 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41967 / 512000) (41971 / 512000) (294534019 / 250000000) (589077243 / 500000000) (1850557 / 500000) (3701291 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41967 / 512000) (41971 / 512000) (1850557 / 500000) (3701291 / 1000000) (6517 / 200) (4074 / 125)
    (1253 / 25) (50221 / 1000) (-276891 / 500) (196297 / 500000) (600569 / 200) (3855849 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1850557 / 500000) (16598164483 / 250000) (3855849 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1850557 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1850557 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell458 :
    ∀ t ∈ Set.Icc ((41971 / 512000) : ℝ) (1679 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235630897 / 200000000) : ℝ) ≤ Real.exp (2 * (41971 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41971 / 512000)) (235630897 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1679 / 20480) : ℝ)) ≤ (235634579 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1679 / 20480)) (235634579 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((33202105627 / 500000) : ℝ) ≤ Real.exp (3 * (925293 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (925293 / 250000)) (33202105627 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41971 / 512000) : ℝ) (1679 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (925293 / 250000) (925337 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41971 / 512000) (1679 / 20480) (235630897 / 200000000) (235634579 / 200000000) (925293 / 250000) (925337 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41971 / 512000) (1679 / 20480) (925293 / 250000) (925337 / 250000) (16293 / 500) (32593 / 1000)
    (50127 / 1000) (12557 / 250) (-138449 / 250) (12267 / 31250) (300303 / 100) (1927589 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (925293 / 250000) (33202105627 / 500000) (1927589 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (925293 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (925293 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell459 :
    ∀ t ∈ Set.Icc ((1679 / 20480) : ℝ) (41979 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((589086447 / 500000000) : ℝ) ≤ Real.exp (2 * (1679 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1679 / 20480)) (589086447 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41979 / 512000) : ℝ)) ≤ (147273913 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41979 / 512000)) (147273913 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66415766587 / 1000000) : ℝ) ≤ Real.exp (3 * (370123 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (370123 / 100000)) (66415766587 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1679 / 20480) : ℝ) (41979 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (370123 / 100000) (1850703 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1679 / 20480) (41979 / 512000) (589086447 / 500000000) (147273913 / 125000000) (370123 / 100000) (1850703 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1679 / 20480) (41979 / 512000) (370123 / 100000) (1850703 / 500000) (32587 / 1000) (6519 / 200)
    (25067 / 500) (10047 / 200) (-276903 / 500) (196247 / 500000) (3003219 / 1000) (3854507 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (370123 / 100000) (66415766587 / 1000000) (3854507 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (370123 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (370123 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch022 :
    ∀ t ∈ Set.Icc ((41899 / 512000) : ℝ) (41979 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell440
      hpThetaDensityLowerExpCompact_cell441)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell442
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell443
      hpThetaDensityLowerExpCompact_cell444)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell445
      hpThetaDensityLowerExpCompact_cell446)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell447
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell448
      hpThetaDensityLowerExpCompact_cell449))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell450
      hpThetaDensityLowerExpCompact_cell451)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell452
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell453
      hpThetaDensityLowerExpCompact_cell454)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell455
      hpThetaDensityLowerExpCompact_cell456)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell457
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell458
      hpThetaDensityLowerExpCompact_cell459)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch022
end HodgeProofHP
