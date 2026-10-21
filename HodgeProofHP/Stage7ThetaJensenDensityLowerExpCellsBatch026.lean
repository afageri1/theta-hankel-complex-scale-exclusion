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
theorem hpThetaDensityLowerExpCompact_cell520 :
    ∀ t ∈ Set.Icc ((42243 / 512000) : ℝ) (42251 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1179406939 / 1000000000) : ℝ) ≤ Real.exp (2 * (42243 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42243 / 512000)) (1179406939 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42251 / 512000) : ℝ)) ≤ (1179443797 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42251 / 512000)) (1179443797 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13438511251 / 200000) : ℝ) ≤ Real.exp (3 * (1852553 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1852553 / 500000)) (13438511251 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42243 / 512000) : ℝ) (42251 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1852553 / 500000) (3705341 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42243 / 512000) (42251 / 512000) (1179406939 / 1000000000) (1179443797 / 1000000000) (1852553 / 500000) (3705341 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42243 / 512000) (42251 / 512000) (1852553 / 500000) (3705341 / 1000000) (32679 / 1000) (4086 / 125)
    (50593 / 1000) (6341 / 125) (-554211 / 1000) (77839 / 200000) (301601 / 100) (1904973 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1852553 / 500000) (13438511251 / 200000) (1904973 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1852553 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1852553 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell521 :
    ∀ t ∈ Set.Icc ((42251 / 512000) : ℝ) (42259 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((294860949 / 250000000) : ℝ) ≤ Real.exp (2 * (42251 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42251 / 512000)) (294860949 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42259 / 512000) : ℝ)) ≤ (73717541 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42259 / 512000)) (73717541 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((33607971661 / 500000) : ℝ) ≤ Real.exp (3 * (1852611 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1852611 / 500000)) (33607971661 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42251 / 512000) : ℝ) (42259 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1852611 / 500000) (3705457 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42251 / 512000) (42259 / 512000) (294860949 / 250000000) (73717541 / 62500000) (1852611 / 500000) (3705457 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42251 / 512000) (42259 / 512000) (1852611 / 500000) (3705457 / 1000000) (32681 / 1000) (32691 / 1000)
    (6326 / 125) (25371 / 500) (-55423 / 100) (389097 / 1000000) (754097 / 250) (3808621 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1852611 / 500000) (33607971661 / 500000) (3808621 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1852611 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1852611 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell522 :
    ∀ t ∈ Set.Icc ((42259 / 512000) : ℝ) (42267 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235896131 / 200000000) : ℝ) ≤ Real.exp (2 * (42259 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42259 / 512000)) (235896131 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42267 / 512000) : ℝ)) ≤ (235903503 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42267 / 512000)) (235903503 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6723933853 / 100000) : ℝ) ≤ Real.exp (3 * (1852669 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1852669 / 500000)) (6723933853 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42259 / 512000) : ℝ) (42267 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1852669 / 500000) (3705573 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42259 / 512000) (42267 / 512000) (235896131 / 200000000) (235903503 / 200000000) (1852669 / 500000) (3705573 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42259 / 512000) (42267 / 512000) (1852669 / 500000) (3705573 / 1000000) (8171 / 250) (16347 / 500)
    (25311 / 500) (12689 / 250) (-2217 / 4) (194499 / 500000) (603353 / 200) (59489 / 15625000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1852669 / 500000) (6723933853 / 100000) (59489 / 15625000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1852669 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1852669 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell523 :
    ∀ t ∈ Set.Icc ((42267 / 512000) : ℝ) (1691 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((589758757 / 500000000) : ℝ) ≤ Real.exp (2 * (42267 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42267 / 512000)) (589758757 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1691 / 20480) : ℝ)) ≤ (1887287 / 1600000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1691 / 20480)) (1887287 / 1600000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1681568547 / 25000) : ℝ) ≤ Real.exp (3 * (1852727 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1852727 / 500000)) (1681568547 / 25000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42267 / 512000) : ℝ) (1691 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1852727 / 500000) (3705689 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42267 / 512000) (1691 / 20480) (589758757 / 500000000) (1887287 / 1600000) (1852727 / 500000) (3705689 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42267 / 512000) (1691 / 20480) (1852727 / 500000) (3705689 / 1000000) (32687 / 1000) (4087 / 125)
    (12659 / 250) (5077 / 100) (-55427 / 100) (388899 / 1000000) (3017143 / 1000) (3805971 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1852727 / 500000) (1681568547 / 25000) (3805971 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1852727 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1852727 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell524 :
    ∀ t ∈ Set.Icc ((1691 / 20480) : ℝ) (42283 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((589777187 / 500000000) : ℝ) ≤ Real.exp (2 * (1691 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1691 / 20480)) (589777187 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42283 / 512000) : ℝ)) ≤ (1179591237 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42283 / 512000)) (1179591237 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2102692293 / 31250) : ℝ) ≤ Real.exp (3 * (370557 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (370557 / 100000)) (2102692293 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1691 / 20480) : ℝ) (42283 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (370557 / 100000) (926451 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1691 / 20480) (42283 / 512000) (589777187 / 500000000) (1179591237 / 1000000000) (370557 / 100000) (926451 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1691 / 20480) (42283 / 512000) (370557 / 100000) (926451 / 250000) (3269 / 100) (32699 / 1000)
    (1013 / 20) (6348 / 125) (-110859 / 200) (243 / 625) (1508759 / 500) (3804647 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (370557 / 100000) (2102692293 / 31250) (3804647 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (370557 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (370557 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell525 :
    ∀ t ∈ Set.Icc ((42283 / 512000) : ℝ) (42291 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((294897809 / 250000000) : ℝ) ≤ Real.exp (2 * (42283 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42283 / 512000)) (294897809 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42291 / 512000) : ℝ)) ≤ (11796281 / 10000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42291 / 512000)) (11796281 / 10000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((67309371093 / 1000000) : ℝ) ≤ Real.exp (3 * (741137 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (741137 / 200000)) (67309371093 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42283 / 512000) : ℝ) (42291 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (741137 / 200000) (11581 / 3125) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42283 / 512000) (42291 / 512000) (294897809 / 250000000) (11796281 / 10000000) (741137 / 200000) (11581 / 3125) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42283 / 512000) (42291 / 512000) (741137 / 200000) (11581 / 3125) (8173 / 250) (16351 / 500)
    (6333 / 125) (25399 / 500) (-55431 / 100) (194351 / 500000) (377237 / 125) (1901667 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (741137 / 200000) (67309371093 / 1000000) (1901667 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (741137 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (741137 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell526 :
    ∀ t ∈ Set.Icc ((42291 / 512000) : ℝ) (42299 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1179628099 / 1000000000) : ℝ) ≤ Real.exp (2 * (42291 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42291 / 512000)) (1179628099 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42299 / 512000) : ℝ)) ≤ (294916241 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42299 / 512000)) (294916241 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((67332798819 / 1000000) : ℝ) ≤ Real.exp (3 * (3705801 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3705801 / 1000000)) (67332798819 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42291 / 512000) : ℝ) (42299 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3705801 / 1000000) (926509 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42291 / 512000) (42299 / 512000) (1179628099 / 1000000000) (294916241 / 250000000) (3705801 / 1000000) (926509 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42291 / 512000) (42299 / 512000) (3705801 / 1000000) (926509 / 250000) (6539 / 200) (6541 / 200)
    (25339 / 500) (50813 / 1000) (-55433 / 100) (388603 / 1000000) (3018273 / 1000) (3802011 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3705801 / 1000000) (67332798819 / 1000000) (3802011 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3705801 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3705801 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell527 :
    ∀ t ∈ Set.Icc ((42299 / 512000) : ℝ) (42307 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1179664963 / 1000000000) : ℝ) ≤ Real.exp (2 * (42299 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42299 / 512000)) (1179664963 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42307 / 512000) : ℝ)) ≤ (1179701829 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42307 / 512000)) (1179701829 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((67356234699 / 1000000) : ℝ) ≤ Real.exp (3 * (3705917 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3705917 / 1000000)) (67356234699 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42299 / 512000) : ℝ) (42307 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3705917 / 1000000) (463269 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42299 / 512000) (42307 / 512000) (1179664963 / 1000000000) (1179701829 / 1000000000) (3705917 / 1000000) (463269 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42299 / 512000) (42307 / 512000) (3705917 / 1000000) (463269 / 125000) (16349 / 500) (32707 / 1000)
    (50693 / 1000) (50827 / 1000) (-554349 / 1000) (77701 / 200000) (3018651 / 1000) (237543 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3705917 / 1000000) (67356234699 / 1000000) (237543 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3705917 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3705917 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell528 :
    ∀ t ∈ Set.Icc ((42307 / 512000) : ℝ) (8463 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((294925457 / 250000000) : ℝ) ≤ Real.exp (2 * (42307 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42307 / 512000)) (294925457 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8463 / 102400) : ℝ)) ≤ (235947739 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8463 / 102400)) (235947739 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((67379678737 / 1000000) : ℝ) ≤ Real.exp (3 * (3706033 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3706033 / 1000000)) (67379678737 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42307 / 512000) : ℝ) (8463 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3706033 / 1000000) (926567 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42307 / 512000) (8463 / 102400) (294925457 / 250000000) (235947739 / 200000000) (3706033 / 1000000) (926567 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42307 / 512000) (8463 / 102400) (3706033 / 1000000) (926567 / 250000) (32701 / 1000) (3271 / 100)
    (50707 / 1000) (50841 / 1000) (-554369 / 1000) (194203 / 500000) (3019029 / 1000) (1899683 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3706033 / 1000000) (67379678737 / 1000000) (1899683 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3706033 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3706033 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell529 :
    ∀ t ∈ Set.Icc ((8463 / 102400) : ℝ) (42323 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((589869347 / 500000000) : ℝ) ≤ Real.exp (2 * (8463 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8463 / 102400)) (589869347 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42323 / 512000) : ℝ)) ≤ (1179775563 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42323 / 512000)) (1179775563 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((33701565467 / 500000) : ℝ) ≤ Real.exp (3 * (3706149 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3706149 / 1000000)) (33701565467 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8463 / 102400) : ℝ) (42323 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3706149 / 1000000) (3706383 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8463 / 102400) (42323 / 512000) (589869347 / 500000000) (1179775563 / 1000000000) (3706149 / 1000000) (3706383 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8463 / 102400) (42323 / 512000) (3706149 / 1000000) (3706383 / 1000000) (32703 / 1000) (32713 / 1000)
    (50721 / 1000) (10171 / 200) (-277197 / 500) (388307 / 1000000) (754851 / 250) (949511 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3706149 / 1000000) (33701565467 / 500000) (949511 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3706149 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3706149 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell530 :
    ∀ t ∈ Set.Icc ((42323 / 512000) : ℝ) (42331 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((589887781 / 500000000) : ℝ) ≤ Real.exp (2 * (42323 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42323 / 512000)) (589887781 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42331 / 512000) : ℝ)) ≤ (1179812431 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42331 / 512000)) (1179812431 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13485277803 / 200000) : ℝ) ≤ Real.exp (3 * (463283 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (463283 / 125000)) (13485277803 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42323 / 512000) : ℝ) (42331 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (463283 / 125000) (3706499 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42323 / 512000) (42331 / 512000) (589887781 / 500000000) (1179812431 / 1000000000) (463283 / 125000) (3706499 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42323 / 512000) (42331 / 512000) (463283 / 125000) (3706499 / 1000000) (16353 / 500) (6543 / 200)
    (10147 / 200) (50869 / 1000) (-554409 / 1000) (388209 / 1000000) (1509891 / 500) (1898367 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (463283 / 125000) (13485277803 / 200000) (1898367 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (463283 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (463283 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell531 :
    ∀ t ∈ Set.Icc ((42331 / 512000) : ℝ) (42339 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((117981243 / 100000000) : ℝ) ≤ Real.exp (2 * (42331 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42331 / 512000)) (117981243 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42339 / 512000) : ℝ)) ≤ (1179849301 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42339 / 512000)) (1179849301 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6744985747 / 100000) : ℝ) ≤ Real.exp (3 * (185319 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (185319 / 50000)) (6744985747 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42331 / 512000) : ℝ) (42339 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (185319 / 50000) (741323 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42331 / 512000) (42339 / 512000) (117981243 / 100000000) (1179849301 / 1000000000) (185319 / 50000) (741323 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42331 / 512000) (42339 / 512000) (185319 / 50000) (741323 / 200000) (32709 / 1000) (16359 / 500)
    (50749 / 1000) (50883 / 1000) (-554429 / 1000) (388111 / 1000000) (75504 / 25) (3795413 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (185319 / 50000) (6744985747 / 100000) (3795413 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (185319 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (185319 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell532 :
    ∀ t ∈ Set.Icc ((42339 / 512000) : ℝ) (42347 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((11798493 / 10000000) : ℝ) ≤ Real.exp (2 * (42339 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42339 / 512000)) (11798493 / 10000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42347 / 512000) : ℝ)) ≤ (294971543 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42347 / 512000)) (294971543 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((33736667047 / 500000) : ℝ) ≤ Real.exp (3 * (57914 / 15625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (57914 / 15625)) (33736667047 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42339 / 512000) : ℝ) (42347 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (57914 / 15625) (3706731 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42339 / 512000) (42347 / 512000) (11798493 / 10000000) (294971543 / 250000000) (57914 / 15625) (3706731 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42339 / 512000) (42347 / 512000) (57914 / 15625) (3706731 / 1000000) (4089 / 125) (32721 / 1000)
    (50763 / 1000) (25449 / 500) (-69306 / 125) (97003 / 250000) (1510269 / 500) (948523 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (57914 / 15625) (33736667047 / 500000) (948523 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (57914 / 15625)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (57914 / 15625)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell533 :
    ∀ t ∈ Set.Icc ((42347 / 512000) : ℝ) (8471 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1179886171 / 1000000000) : ℝ) ≤ Real.exp (2 * (42347 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42347 / 512000)) (1179886171 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8471 / 102400) : ℝ)) ≤ (294980761 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8471 / 102400)) (294980761 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((67496818889 / 1000000) : ℝ) ≤ Real.exp (3 * (926653 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (926653 / 250000)) (67496818889 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42347 / 512000) : ℝ) (8471 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (926653 / 250000) (3706847 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42347 / 512000) (8471 / 102400) (1179886171 / 1000000000) (294980761 / 250000000) (926653 / 250000) (3706847 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42347 / 512000) (8471 / 102400) (926653 / 250000) (3706847 / 1000000) (16357 / 500) (8181 / 250)
    (25389 / 500) (6364 / 125) (-138617 / 250) (193957 / 500000) (755229 / 250) (948193 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (926653 / 250000) (67496818889 / 1000000) (948193 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (926653 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (926653 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell534 :
    ∀ t ∈ Set.Icc ((8471 / 102400) : ℝ) (42363 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1179923043 / 1000000000) : ℝ) ≤ Real.exp (2 * (8471 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8471 / 102400)) (1179923043 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42363 / 512000) : ℝ)) ≤ (1179959917 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42363 / 512000)) (1179959917 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((33760155929 / 500000) : ℝ) ≤ Real.exp (3 * (463341 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (463341 / 125000)) (33760155929 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8471 / 102400) : ℝ) (42363 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (463341 / 125000) (3706963 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8471 / 102400) (42363 / 512000) (1179923043 / 1000000000) (1179959917 / 1000000000) (463341 / 125000) (3706963 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8471 / 102400) (42363 / 512000) (463341 / 125000) (3706963 / 1000000) (32717 / 1000) (16363 / 500)
    (6349 / 125) (25463 / 500) (-69311 / 125) (77563 / 200000) (1510647 / 500) (947863 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (463341 / 125000) (33760155929 / 500000) (947863 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (463341 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (463341 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell535 :
    ∀ t ∈ Set.Icc ((42363 / 512000) : ℝ) (42371 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((294989979 / 250000000) : ℝ) ≤ Real.exp (2 * (42363 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42363 / 512000)) (294989979 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42371 / 512000) : ℝ)) ≤ (1179996791 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42371 / 512000)) (1179996791 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16885953251 / 250000) : ℝ) ≤ Real.exp (3 * (926711 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (926711 / 250000)) (16885953251 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42363 / 512000) : ℝ) (42371 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (926711 / 250000) (1853539 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42363 / 512000) (42371 / 512000) (294989979 / 250000000) (1179996791 / 1000000000) (926711 / 250000) (1853539 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42363 / 512000) (42371 / 512000) (926711 / 250000) (1853539 / 500000) (818 / 25) (32729 / 1000)
    (25403 / 500) (2547 / 50) (-69314 / 125) (96929 / 250000) (3021669 / 1000) (3790133 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (926711 / 250000) (16885953251 / 250000) (3790133 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (926711 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (926711 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell536 :
    ∀ t ∈ Set.Icc ((42371 / 512000) : ℝ) (42379 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((117999679 / 100000000) : ℝ) ≤ Real.exp (2 * (42371 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42371 / 512000)) (117999679 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42379 / 512000) : ℝ)) ≤ (1180033667 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42379 / 512000)) (1180033667 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16891779907 / 250000) : ℝ) ≤ Real.exp (3 * (3706959 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3706959 / 1000000)) (16891779907 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42371 / 512000) : ℝ) (42379 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3706959 / 1000000) (1853597 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42371 / 512000) (42379 / 512000) (117999679 / 100000000) (1180033667 / 1000000000) (3706959 / 1000000) (1853597 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42371 / 512000) (42379 / 512000) (3706959 / 1000000) (1853597 / 500000) (32723 / 1000) (8183 / 250)
    (2541 / 50) (25477 / 500) (-554527 / 1000) (387619 / 1000000) (377756 / 125) (1894413 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3706959 / 1000000) (16891779907 / 250000) (1894413 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3706959 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3706959 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell537 :
    ∀ t ∈ Set.Icc ((42379 / 512000) : ℝ) (42387 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((590016833 / 500000000) : ℝ) ≤ Real.exp (2 * (42379 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42379 / 512000)) (590016833 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42387 / 512000) : ℝ)) ≤ (1180070543 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42387 / 512000)) (1180070543 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((33795318533 / 500000) : ℝ) ≤ Real.exp (3 * (148283 / 40000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (148283 / 40000)) (33795318533 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42379 / 512000) : ℝ) (42387 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (148283 / 40000) (370731 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42379 / 512000) (42387 / 512000) (590016833 / 500000000) (1180070543 / 1000000000) (148283 / 40000) (370731 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42379 / 512000) (42387 / 512000) (148283 / 40000) (370731 / 100000) (1309 / 40) (6547 / 200)
    (25417 / 500) (50969 / 1000) (-554547 / 1000) (1211 / 3125) (1511213 / 500) (3787507 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (148283 / 40000) (33795318533 / 500000) (3787507 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (148283 / 40000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (148283 / 40000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell538 :
    ∀ t ∈ Set.Icc ((42387 / 512000) : ℝ) (8479 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((590035271 / 500000000) : ℝ) ≤ Real.exp (2 * (42387 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42387 / 512000)) (590035271 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8479 / 102400) : ℝ)) ≤ (1180107421 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8479 / 102400)) (1180107421 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6761416269 / 100000) : ℝ) ≤ Real.exp (3 * (3707191 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3707191 / 1000000)) (6761416269 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42387 / 512000) : ℝ) (8479 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3707191 / 1000000) (1853713 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42387 / 512000) (8479 / 102400) (590035271 / 500000000) (1180107421 / 1000000000) (3707191 / 1000000) (1853713 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42387 / 512000) (8479 / 102400) (3707191 / 1000000) (1853713 / 500000) (4091 / 125) (32737 / 1000)
    (6356 / 125) (50983 / 1000) (-554567 / 1000) (193711 / 500000) (755701 / 250) (378619 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3707191 / 1000000) (6761416269 / 100000) (378619 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3707191 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3707191 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell539 :
    ∀ t ∈ Set.Icc ((8479 / 102400) : ℝ) (42403 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((59005371 / 50000000) : ℝ) ≤ Real.exp (2 * (8479 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8479 / 102400)) (59005371 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42403 / 512000) : ℝ)) ≤ (11801443 / 10000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42403 / 512000)) (11801443 / 10000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((33818848251 / 500000) : ℝ) ≤ Real.exp (3 * (3707307 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3707307 / 1000000)) (33818848251 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8479 / 102400) : ℝ) (42403 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3707307 / 1000000) (1853771 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8479 / 102400) (42403 / 512000) (59005371 / 50000000) (11801443 / 10000000) (3707307 / 1000000) (1853771 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8479 / 102400) (42403 / 512000) (3707307 / 1000000) (1853771 / 500000) (32731 / 1000) (1637 / 50)
    (50863 / 1000) (50997 / 1000) (-554587 / 1000) (387323 / 1000000) (3023183 / 1000) (473109 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3707307 / 1000000) (33818848251 / 500000) (473109 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3707307 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3707307 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch026 :
    ∀ t ∈ Set.Icc ((42243 / 512000) : ℝ) (42403 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell520
      hpThetaDensityLowerExpCompact_cell521)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell522
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell523
      hpThetaDensityLowerExpCompact_cell524)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell525
      hpThetaDensityLowerExpCompact_cell526)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell527
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell528
      hpThetaDensityLowerExpCompact_cell529))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell530
      hpThetaDensityLowerExpCompact_cell531)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell532
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell533
      hpThetaDensityLowerExpCompact_cell534)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell535
      hpThetaDensityLowerExpCompact_cell536)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell537
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell538
      hpThetaDensityLowerExpCompact_cell539)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch026
end HodgeProofHP
