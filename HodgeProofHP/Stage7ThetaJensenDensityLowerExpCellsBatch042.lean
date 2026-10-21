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
theorem hpThetaDensityLowerExpCompact_cell840 :
    ∀ t ∈ Set.Icc ((45987 / 512000) : ℝ) (46003 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((239356503 / 200000000) : ℝ) ≤ Real.exp (2 * (45987 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45987 / 512000)) (239356503 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46003 / 512000) : ℝ)) ≤ (1196857317 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46003 / 512000)) (1196857317 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3165922731 / 40000) : ℝ) ≤ Real.exp (3 * (939923 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (939923 / 250000)) (3165922731 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45987 / 512000) : ℝ) (46003 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (939923 / 250000) (3760047 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45987 / 512000) (46003 / 512000) (239356503 / 200000000) (1196857317 / 1000000000) (939923 / 250000) (3760047 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45987 / 512000) (46003 / 512000) (939923 / 250000) (3760047 / 1000000) (1699 / 50) (16997 / 500)
    (57411 / 1000) (28809 / 500) (-562281 / 1000) (172629 / 500000) (799527 / 250) (646889 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (939923 / 250000) (3165922731 / 40000) (646889 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (939923 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (939923 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell841 :
    ∀ t ∈ Set.Icc ((46003 / 512000) : ℝ) (46019 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((299214329 / 250000000) : ℝ) ≤ Real.exp (2 * (46003 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46003 / 512000)) (299214329 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46019 / 512000) : ℝ)) ≤ (1196932123 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46019 / 512000)) (1196932123 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((79203887301 / 1000000) : ℝ) ≤ Real.exp (3 * (3759927 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3759927 / 1000000)) (79203887301 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46003 / 512000) : ℝ) (46019 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3759927 / 1000000) (1880141 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46003 / 512000) (46019 / 512000) (299214329 / 250000000) (1196932123 / 1000000000) (3759927 / 1000000) (1880141 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46003 / 512000) (46019 / 512000) (3759927 / 1000000) (1880141 / 500000) (16993 / 500) (34)
    (57441 / 1000) (7206 / 125) (-112463 / 200) (345079 / 1000000) (799727 / 250) (646433 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3759927 / 1000000) (79203887301 / 1000000) (646433 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3759927 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3759927 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell842 :
    ∀ t ∈ Set.Icc ((46019 / 512000) : ℝ) (9207 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((598466061 / 500000000) : ℝ) ≤ Real.exp (2 * (46019 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46019 / 512000)) (598466061 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9207 / 102400) : ℝ)) ≤ (598503467 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9207 / 102400)) (598503467 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((39629872847 / 500000) : ℝ) ≤ Real.exp (3 * (1880081 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1880081 / 500000)) (39629872847 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46019 / 512000) : ℝ) (9207 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1880081 / 500000) (3760517 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46019 / 512000) (9207 / 102400) (598466061 / 500000000) (598503467 / 500000000) (1880081 / 500000) (3760517 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46019 / 512000) (9207 / 102400) (1880081 / 500000) (3760517 / 1000000) (4249 / 125) (6801 / 200)
    (57471 / 1000) (28839 / 500) (-562349 / 1000) (344901 / 1000000) (3199707 / 1000) (3229887 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1880081 / 500000) (39629872847 / 500000) (3229887 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1880081 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1880081 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell843 :
    ∀ t ∈ Set.Icc ((9207 / 102400) : ℝ) (46051 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1197006933 / 1000000000) : ℝ) ≤ Real.exp (2 * (9207 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9207 / 102400)) (1197006933 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46051 / 512000) : ℝ)) ≤ (1197081749 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46051 / 512000)) (1197081749 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1982891087 / 25000) : ℝ) ≤ Real.exp (3 * (3760397 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3760397 / 1000000)) (1982891087 / 25000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9207 / 102400) : ℝ) (46051 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3760397 / 1000000) (3760753 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9207 / 102400) (46051 / 512000) (1197006933 / 1000000000) (1197081749 / 1000000000) (3760397 / 1000000) (3760753 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9207 / 102400) (46051 / 512000) (3760397 / 1000000) (3760753 / 1000000) (33997 / 1000) (34011 / 1000)
    (57501 / 1000) (57709 / 1000) (-281189 / 500) (344723 / 1000000) (3200511 / 1000) (3227611 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3760397 / 1000000) (1982891087 / 25000) (3227611 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3760397 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3760397 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell844 :
    ∀ t ∈ Set.Icc ((46051 / 512000) : ℝ) (46067 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((299270437 / 250000000) : ℝ) ≤ Real.exp (2 * (46051 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46051 / 512000)) (299270437 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46067 / 512000) : ℝ)) ≤ (1197156569 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46067 / 512000)) (1197156569 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4960723793 / 62500) : ℝ) ≤ Real.exp (3 * (470079 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (470079 / 125000)) (4960723793 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46051 / 512000) : ℝ) (46067 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (470079 / 125000) (940247 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46051 / 512000) (46067 / 512000) (299270437 / 250000000) (1197156569 / 1000000000) (470079 / 125000) (940247 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46051 / 512000) (46067 / 512000) (470079 / 125000) (940247 / 250000) (34003 / 1000) (34017 / 1000)
    (14383 / 250) (57739 / 1000) (-140603 / 250) (10767 / 31250) (3201311 / 1000) (403167 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (470079 / 125000) (4960723793 / 62500) (403167 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (470079 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (470079 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell845 :
    ∀ t ∈ Set.Icc ((46067 / 512000) : ℝ) (46083 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((149644571 / 125000000) : ℝ) ≤ Real.exp (2 * (46067 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46067 / 512000)) (149644571 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46083 / 512000) : ℝ)) ≤ (598615697 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46083 / 512000)) (598615697 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((39713778673 / 500000) : ℝ) ≤ Real.exp (3 * (3760867 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3760867 / 1000000)) (39713778673 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46067 / 512000) : ℝ) (46083 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3760867 / 1000000) (3761223 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46067 / 512000) (46083 / 512000) (149644571 / 125000000) (598615697 / 500000000) (3760867 / 1000000) (3761223 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46067 / 512000) (46083 / 512000) (3760867 / 1000000) (3761223 / 1000000) (34009 / 1000) (17011 / 500)
    (28781 / 500) (57769 / 1000) (-112489 / 200) (172183 / 500000) (3202111 / 1000) (3223063 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3760867 / 1000000) (39713778673 / 500000) (3223063 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3760867 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3760867 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell846 :
    ∀ t ∈ Set.Icc ((46083 / 512000) : ℝ) (46099 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1197231393 / 1000000000) : ℝ) ≤ Real.exp (2 * (46083 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46083 / 512000)) (1197231393 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46099 / 512000) : ℝ)) ≤ (1197306223 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46099 / 512000)) (1197306223 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((79483573481 / 1000000) : ℝ) ≤ Real.exp (3 * (1880551 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1880551 / 500000)) (79483573481 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46083 / 512000) : ℝ) (46099 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1880551 / 500000) (1880729 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46083 / 512000) (46099 / 512000) (1197231393 / 1000000000) (1197306223 / 1000000000) (1880551 / 500000) (1880729 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46083 / 512000) (46099 / 512000) (1880551 / 500000) (1880729 / 500000) (17007 / 500) (8507 / 250)
    (7199 / 125) (289 / 5) (-562479 / 1000) (86047 / 250000) (3202911 / 1000) (402599 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1880551 / 500000) (79483573481 / 1000000) (402599 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1880551 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1880551 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell847 :
    ∀ t ∈ Set.Icc ((46099 / 512000) : ℝ) (9223 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((598653111 / 500000000) : ℝ) ≤ Real.exp (2 * (46099 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46099 / 512000)) (598653111 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9223 / 102400) : ℝ)) ≤ (1197381057 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9223 / 102400)) (1197381057 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((39769814561 / 500000) : ℝ) ≤ Real.exp (3 * (3761337 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3761337 / 1000000)) (39769814561 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46099 / 512000) : ℝ) (9223 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3761337 / 1000000) (3761693 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46099 / 512000) (9223 / 102400) (598653111 / 500000000) (1197381057 / 1000000000) (3761337 / 1000000) (3761693 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46099 / 512000) (9223 / 102400) (3761337 / 1000000) (3761693 / 1000000) (1701 / 50) (17017 / 500)
    (28811 / 500) (5783 / 100) (-562513 / 1000) (34401 / 100000) (400464 / 125) (1609261 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3761337 / 1000000) (39769814561 / 500000) (1609261 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3761337 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3761337 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell848 :
    ∀ t ∈ Set.Icc ((9223 / 102400) : ℝ) (46131 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((18709079 / 15625000) : ℝ) ≤ Real.exp (2 * (9223 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9223 / 102400)) (18709079 / 15625000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46131 / 512000) : ℝ)) ≤ (149681987 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46131 / 512000)) (149681987 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15919144859 / 200000) : ℝ) ≤ Real.exp (3 * (940393 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (940393 / 250000)) (15919144859 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9223 / 102400) : ℝ) (46131 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (940393 / 250000) (470241 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9223 / 102400) (46131 / 512000) (18709079 / 15625000) (149681987 / 125000000) (940393 / 250000) (470241 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9223 / 102400) (46131 / 512000) (940393 / 250000) (470241 / 125000) (17013 / 500) (34039 / 1000)
    (57653 / 1000) (2893 / 50) (-281273 / 500) (42979 / 125000) (400564 / 125) (1608127 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (940393 / 250000) (15919144859 / 200000) (1608127 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (940393 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (940393 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell849 :
    ∀ t ∈ Set.Icc ((46131 / 512000) : ℝ) (46147 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((239491179 / 200000000) : ℝ) ≤ Real.exp (2 * (46131 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46131 / 512000)) (239491179 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46147 / 512000) : ℝ)) ≤ (1197530739 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46147 / 512000)) (1197530739 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((79651859029 / 1000000) : ℝ) ≤ Real.exp (3 * (3761807 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3761807 / 1000000)) (79651859029 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46131 / 512000) : ℝ) (46147 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3761807 / 1000000) (3762163 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46131 / 512000) (46147 / 512000) (239491179 / 200000000) (1197530739 / 1000000000) (3761807 / 1000000) (3762163 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46131 / 512000) (46147 / 512000) (3761807 / 1000000) (3762163 / 1000000) (34031 / 1000) (6809 / 200)
    (57683 / 1000) (57891 / 1000) (-28129 / 50) (171827 / 500000) (3205313 / 1000) (3213987 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3761807 / 1000000) (79651859029 / 1000000) (3213987 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3761807 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3761807 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell850 :
    ∀ t ∈ Set.Icc ((46147 / 512000) : ℝ) (46163 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((598765369 / 500000000) : ℝ) ≤ Real.exp (2 * (46147 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46147 / 512000)) (598765369 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46163 / 512000) : ℝ)) ≤ (1197605587 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46163 / 512000)) (1197605587 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((79708033353 / 1000000) : ℝ) ≤ Real.exp (3 * (1881021 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1881021 / 500000)) (79708033353 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46147 / 512000) : ℝ) (46163 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1881021 / 500000) (1881199 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46147 / 512000) (46163 / 512000) (598765369 / 500000000) (1197605587 / 1000000000) (1881021 / 500000) (1881199 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46147 / 512000) (46163 / 512000) (1881021 / 500000) (1881199 / 500000) (34037 / 1000) (34051 / 1000)
    (57713 / 1000) (57921 / 1000) (-562613 / 1000) (85869 / 250000) (1603057 / 500) (1605861 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1881021 / 500000) (79708033353 / 1000000) (1605861 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1881021 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1881021 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell851 :
    ∀ t ∈ Set.Icc ((46163 / 512000) : ℝ) (46179 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((598802793 / 500000000) : ℝ) ≤ Real.exp (2 * (46163 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46163 / 512000)) (598802793 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46179 / 512000) : ℝ)) ≤ (29942011 / 25000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46179 / 512000)) (29942011 / 25000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((79764247293 / 1000000) : ℝ) ≤ Real.exp (3 * (3762277 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3762277 / 1000000)) (79764247293 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46163 / 512000) : ℝ) (46179 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3762277 / 1000000) (3762633 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46163 / 512000) (46179 / 512000) (598802793 / 500000000) (29942011 / 25000000) (3762277 / 1000000) (3762633 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46163 / 512000) (46179 / 512000) (3762277 / 1000000) (3762633 / 1000000) (34043 / 1000) (4257 / 125)
    (7218 / 125) (57951 / 1000) (-562647 / 1000) (171649 / 500000) (641383 / 200) (1604729 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3762277 / 1000000) (79764247293 / 1000000) (1604729 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3762277 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3762277 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell852 :
    ∀ t ∈ Set.Icc ((46179 / 512000) : ℝ) (9239 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1197680439 / 1000000000) : ℝ) ≤ Real.exp (2 * (46179 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46179 / 512000)) (1197680439 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9239 / 102400) : ℝ)) ≤ (1197755297 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9239 / 102400)) (1197755297 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((79820740339 / 1000000) : ℝ) ≤ Real.exp (3 * (3762513 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3762513 / 1000000)) (79820740339 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46179 / 512000) : ℝ) (9239 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3762513 / 1000000) (3762869 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46179 / 512000) (9239 / 102400) (1197680439 / 1000000000) (1197755297 / 1000000000) (3762513 / 1000000) (3762869 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46179 / 512000) (9239 / 102400) (3762513 / 1000000) (3762869 / 1000000) (4256 / 125) (17031 / 500)
    (28887 / 500) (28991 / 500) (-14067 / 25) (4289 / 12500) (80193 / 25) (3207187 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3762513 / 1000000) (79820740339 / 1000000) (3207187 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3762513 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3762513 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell853 :
    ∀ t ∈ Set.Icc ((9239 / 102400) : ℝ) (46211 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((37429853 / 31250000) : ℝ) ≤ Real.exp (2 * (9239 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9239 / 102400)) (37429853 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46211 / 512000) : ℝ)) ≤ (1197830159 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46211 / 512000)) (1197830159 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((39938516883 / 500000) : ℝ) ≤ Real.exp (3 * (940687 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (940687 / 250000)) (39938516883 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9239 / 102400) : ℝ) (46211 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (940687 / 250000) (117597 / 31250) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9239 / 102400) (46211 / 512000) (37429853 / 31250000) (1197830159 / 1000000000) (940687 / 250000) (117597 / 31250) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9239 / 102400) (46211 / 512000) (940687 / 250000) (117597 / 31250) (17027 / 500) (8517 / 250)
    (14451 / 250) (14503 / 250) (-281357 / 500) (171471 / 500000) (3208521 / 1000) (3204927 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (940687 / 250000) (39938516883 / 500000) (3204927 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (940687 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (940687 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell854 :
    ∀ t ∈ Set.Icc ((46211 / 512000) : ℝ) (46227 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((598915079 / 500000000) : ℝ) ≤ Real.exp (2 * (46211 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46211 / 512000)) (598915079 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46227 / 512000) : ℝ)) ≤ (598952513 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46227 / 512000)) (598952513 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((79933366893 / 1000000) : ℝ) ≤ Real.exp (3 * (3762983 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3762983 / 1000000)) (79933366893 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46211 / 512000) : ℝ) (46227 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3762983 / 1000000) (3763339 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46211 / 512000) (46227 / 512000) (598915079 / 500000000) (598952513 / 500000000) (3762983 / 1000000) (3763339 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46211 / 512000) (46227 / 512000) (3762983 / 1000000) (3763339 / 1000000) (1703 / 50) (34073 / 1000)
    (11567 / 200) (29021 / 500) (-562747 / 1000) (68553 / 200000) (3209323 / 1000) (800667 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3762983 / 1000000) (79933366893 / 1000000) (800667 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3762983 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3762983 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell855 :
    ∀ t ∈ Set.Icc ((46227 / 512000) : ℝ) (46243 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((47916201 / 40000000) : ℝ) ≤ Real.exp (2 * (46227 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46227 / 512000)) (47916201 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46243 / 512000) : ℝ)) ≤ (1197979897 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46243 / 512000)) (1197979897 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((79989739749 / 1000000) : ℝ) ≤ Real.exp (3 * (1881609 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1881609 / 500000)) (79989739749 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46227 / 512000) : ℝ) (46243 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1881609 / 500000) (1881787 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46227 / 512000) (46243 / 512000) (47916201 / 40000000) (1197979897 / 1000000000) (1881609 / 500000) (1881787 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46227 / 512000) (46243 / 512000) (1881609 / 500000) (1881787 / 500000) (6813 / 200) (34079 / 1000)
    (11573 / 200) (58073 / 1000) (-562781 / 1000) (342587 / 1000000) (25681 / 8) (3200411 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1881609 / 500000) (79989739749 / 1000000) (3200411 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1881609 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1881609 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell856 :
    ∀ t ∈ Set.Icc ((46243 / 512000) : ℝ) (46259 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((149747487 / 125000000) : ℝ) ≤ Real.exp (2 * (46243 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46243 / 512000)) (149747487 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46259 / 512000) : ℝ)) ≤ (1198054773 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46259 / 512000)) (1198054773 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((40023076181 / 500000) : ℝ) ≤ Real.exp (3 * (3763453 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3763453 / 1000000)) (40023076181 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46243 / 512000) : ℝ) (46259 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3763453 / 1000000) (3763809 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46243 / 512000) (46259 / 512000) (149747487 / 125000000) (1198054773 / 1000000000) (3763453 / 1000000) (3763809 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46243 / 512000) (46259 / 512000) (3763453 / 1000000) (3763809 / 1000000) (34071 / 1000) (6817 / 200)
    (11579 / 200) (58103 / 1000) (-281407 / 500) (34241 / 100000) (1605463 / 500) (639631 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3763453 / 1000000) (40023076181 / 500000) (639631 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3763453 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3763453 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell857 :
    ∀ t ∈ Set.Icc ((46259 / 512000) : ℝ) (1851 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((299513693 / 250000000) : ℝ) ≤ Real.exp (2 * (46259 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46259 / 512000)) (299513693 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1851 / 20480) : ℝ)) ≤ (599064827 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1851 / 20480)) (599064827 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((80102845067 / 1000000) : ℝ) ≤ Real.exp (3 * (3763689 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3763689 / 1000000)) (80102845067 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46259 / 512000) : ℝ) (1851 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3763689 / 1000000) (752809 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46259 / 512000) (1851 / 20480) (299513693 / 250000000) (599064827 / 500000000) (3763689 / 1000000) (752809 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46259 / 512000) (1851 / 20480) (3763689 / 1000000) (752809 / 200000) (34077 / 1000) (34091 / 1000)
    (28963 / 500) (58133 / 1000) (-70356 / 125) (42779 / 125000) (802933 / 250) (798973 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3763689 / 1000000) (80102845067 / 1000000) (798973 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3763689 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3763689 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell858 :
    ∀ t ∈ Set.Icc ((1851 / 20480) : ℝ) (46291 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1198129653 / 1000000000) : ℝ) ≤ Real.exp (2 * (1851 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1851 / 20480)) (1198129653 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46291 / 512000) : ℝ)) ≤ (1198204539 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46291 / 512000)) (1198204539 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((80159337447 / 1000000) : ℝ) ≤ Real.exp (3 * (940981 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (940981 / 250000)) (80159337447 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1851 / 20480) : ℝ) (46291 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (940981 / 250000) (94107 / 25000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1851 / 20480) (46291 / 512000) (1198129653 / 1000000000) (1198204539 / 1000000000) (940981 / 250000) (94107 / 25000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1851 / 20480) (46291 / 512000) (940981 / 250000) (94107 / 25000) (17041 / 500) (4262 / 125)
    (14489 / 250) (14541 / 250) (-562881 / 1000) (68411 / 200000) (1606267 / 500) (79841 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (940981 / 250000) (80159337447 / 1000000) (79841 / 25000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (940981 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (940981 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell859 :
    ∀ t ∈ Set.Icc ((46291 / 512000) : ℝ) (46307 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((599102269 / 500000000) : ℝ) ≤ Real.exp (2 * (46291 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46291 / 512000)) (599102269 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46307 / 512000) : ℝ)) ≤ (119827943 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46307 / 512000)) (119827943 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((20053967417 / 250000) : ℝ) ≤ Real.exp (3 * (3764159 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3764159 / 1000000)) (20053967417 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46291 / 512000) : ℝ) (46307 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3764159 / 1000000) (752903 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46291 / 512000) (46307 / 512000) (599102269 / 500000000) (119827943 / 100000000) (3764159 / 1000000) (752903 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46291 / 512000) (46307 / 512000) (3764159 / 1000000) (752903 / 200000) (4261 / 125) (17051 / 500)
    (28993 / 500) (29097 / 500) (-281457 / 500) (170939 / 500000) (401667 / 125) (3191389 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3764159 / 1000000) (20053967417 / 250000) (3191389 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3764159 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3764159 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch042 :
    ∀ t ∈ Set.Icc ((45987 / 512000) : ℝ) (46307 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell840
      hpThetaDensityLowerExpCompact_cell841)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell842
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell843
      hpThetaDensityLowerExpCompact_cell844)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell845
      hpThetaDensityLowerExpCompact_cell846)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell847
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell848
      hpThetaDensityLowerExpCompact_cell849))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell850
      hpThetaDensityLowerExpCompact_cell851)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell852
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell853
      hpThetaDensityLowerExpCompact_cell854)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell855
      hpThetaDensityLowerExpCompact_cell856)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell857
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell858
      hpThetaDensityLowerExpCompact_cell859)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch042
end HodgeProofHP
