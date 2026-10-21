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
theorem hpThetaDensityLowerExpCompact_cell620 :
    ∀ t ∈ Set.Icc ((43043 / 512000) : ℝ) (43051 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1183098351 / 1000000000) : ℝ) ≤ Real.exp (2 * (43043 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43043 / 512000)) (1183098351 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43051 / 512000) : ℝ)) ≤ (295783831 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43051 / 512000)) (295783831 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((34785696201 / 500000) : ℝ) ≤ Real.exp (3 * (3716703 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3716703 / 1000000)) (34785696201 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43043 / 512000) : ℝ) (43051 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3716703 / 1000000) (1858469 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43043 / 512000) (43051 / 512000) (1183098351 / 1000000000) (295783831 / 250000000) (3716703 / 1000000) (1858469 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43043 / 512000) (43051 / 512000) (3716703 / 1000000) (1858469 / 500000) (32953 / 1000) (32963 / 1000)
    (26009 / 500) (52153 / 1000) (-278083 / 500) (94857 / 250000) (1526973 / 500) (1839837 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3716703 / 1000000) (34785696201 / 500000) (1839837 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3716703 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3716703 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell621 :
    ∀ t ∈ Set.Icc ((43051 / 512000) : ℝ) (43059 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1183135323 / 1000000000) : ℝ) ≤ Real.exp (2 * (43051 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43051 / 512000)) (1183135323 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43059 / 512000) : ℝ)) ≤ (591586149 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43059 / 512000)) (591586149 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8699450931 / 125000) : ℝ) ≤ Real.exp (3 * (3716819 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3716819 / 1000000)) (8699450931 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43051 / 512000) : ℝ) (43059 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3716819 / 1000000) (743411 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43051 / 512000) (43059 / 512000) (1183135323 / 1000000000) (591586149 / 500000000) (3716819 / 1000000) (743411 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43051 / 512000) (43059 / 512000) (3716819 / 1000000) (743411 / 200000) (8239 / 250) (16483 / 500)
    (6504 / 125) (52167 / 1000) (-556181 / 1000) (94833 / 250000) (305433 / 100) (1839197 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3716819 / 1000000) (8699450931 / 125000) (1839197 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3716819 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3716819 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell622 :
    ∀ t ∈ Set.Icc ((43059 / 512000) : ℝ) (43067 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1183172297 / 1000000000) : ℝ) ≤ Real.exp (2 * (43059 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43059 / 512000)) (1183172297 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43067 / 512000) : ℝ)) ≤ (147901159 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43067 / 512000)) (147901159 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((69619830921 / 1000000) : ℝ) ≤ Real.exp (3 * (743387 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (743387 / 200000)) (69619830921 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43059 / 512000) : ℝ) (43067 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (743387 / 200000) (3717171 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43059 / 512000) (43067 / 512000) (1183172297 / 1000000000) (147901159 / 125000000) (743387 / 200000) (3717171 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43059 / 512000) (43067 / 512000) (743387 / 200000) (3717171 / 1000000) (32959 / 1000) (4121 / 125)
    (26023 / 500) (26091 / 500) (-2781 / 5) (94809 / 250000) (381839 / 125) (1838557 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (743387 / 200000) (69619830921 / 1000000) (1838557 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (743387 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (743387 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell623 :
    ∀ t ∈ Set.Icc ((43067 / 512000) : ℝ) (1723 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1183209271 / 1000000000) : ℝ) ≤ Real.exp (2 * (43067 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43067 / 512000)) (1183209271 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1723 / 20480) : ℝ)) ≤ (147905781 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1723 / 20480)) (147905781 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((34822031413 / 500000) : ℝ) ≤ Real.exp (3 * (3717051 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3717051 / 1000000)) (34822031413 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43067 / 512000) : ℝ) (1723 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3717051 / 1000000) (3717287 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43067 / 512000) (1723 / 20480) (1183209271 / 1000000000) (147905781 / 125000000) (3717051 / 1000000) (3717287 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43067 / 512000) (1723 / 20480) (3717051 / 1000000) (3717287 / 1000000) (16481 / 500) (32971 / 1000)
    (52061 / 1000) (13049 / 250) (-27811 / 50) (379139 / 1000000) (3055093 / 1000) (1837917 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3717051 / 1000000) (34822031413 / 500000) (1837917 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3717051 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3717051 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell624 :
    ∀ t ∈ Set.Icc ((1723 / 20480) : ℝ) (43083 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1183246247 / 1000000000) : ℝ) ≤ Real.exp (2 * (1723 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1723 / 20480)) (1183246247 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43083 / 512000) : ℝ)) ≤ (47331329 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43083 / 512000)) (47331329 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6966851217 / 100000) : ℝ) ≤ Real.exp (3 * (232323 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (232323 / 62500)) (6966851217 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1723 / 20480) : ℝ) (43083 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (232323 / 62500) (3717403 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1723 / 20480) (43083 / 512000) (1183246247 / 1000000000) (47331329 / 40000000) (232323 / 62500) (3717403 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1723 / 20480) (43083 / 512000) (232323 / 62500) (3717403 / 1000000) (8241 / 250) (16487 / 500)
    (2083 / 40) (5221 / 100) (-139061 / 250) (379041 / 1000000) (1527737 / 500) (229659 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (232323 / 62500) (6966851217 / 100000) (229659 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (232323 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (232323 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell625 :
    ∀ t ∈ Set.Icc ((43083 / 512000) : ℝ) (43091 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((147910403 / 125000000) : ℝ) ≤ Real.exp (2 * (43083 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43083 / 512000)) (147910403 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43091 / 512000) : ℝ)) ≤ (295830051 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43091 / 512000)) (295830051 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((69692761019 / 1000000) : ℝ) ≤ Real.exp (3 * (929321 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (929321 / 250000)) (69692761019 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43083 / 512000) : ℝ) (43091 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (929321 / 250000) (3717519 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43083 / 512000) (43091 / 512000) (147910403 / 125000000) (295830051 / 250000000) (929321 / 250000) (3717519 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43083 / 512000) (43091 / 512000) (929321 / 250000) (3717519 / 1000000) (32967 / 1000) (32977 / 1000)
    (5209 / 100) (2089 / 40) (-556263 / 1000) (75789 / 200000) (381982 / 125) (1836633 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (929321 / 250000) (69692761019 / 1000000) (1836633 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (929321 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (929321 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell626 :
    ∀ t ∈ Set.Icc ((43091 / 512000) : ℝ) (43099 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1183320203 / 1000000000) : ℝ) ≤ Real.exp (2 * (43091 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43091 / 512000)) (1183320203 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43099 / 512000) : ℝ)) ≤ (1183357183 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43099 / 512000)) (1183357183 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((17429254577 / 250000) : ℝ) ≤ Real.exp (3 * (18587 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (18587 / 5000)) (17429254577 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43091 / 512000) : ℝ) (43099 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (18587 / 5000) (743527 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43091 / 512000) (43099 / 512000) (1183320203 / 1000000000) (1183357183 / 1000000000) (18587 / 5000) (743527 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43091 / 512000) (43099 / 512000) (18587 / 5000) (743527 / 200000) (3297 / 100) (32979 / 1000)
    (6513 / 125) (52239 / 1000) (-278141 / 500) (378849 / 1000000) (3056237 / 1000) (917997 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (18587 / 5000) (17429254577 / 250000) (917997 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (18587 / 5000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (18587 / 5000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell627 :
    ∀ t ∈ Set.Icc ((43099 / 512000) : ℝ) (43107 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((591678591 / 500000000) : ℝ) ≤ Real.exp (2 * (43099 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43099 / 512000)) (591678591 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43107 / 512000) : ℝ)) ≤ (1183394163 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43107 / 512000)) (1183394163 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1743532101 / 25000) : ℝ) ≤ Real.exp (3 * (929379 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (929379 / 250000)) (1743532101 / 25000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43099 / 512000) : ℝ) (43107 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (929379 / 250000) (464719 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43099 / 512000) (43107 / 512000) (591678591 / 500000000) (1183394163 / 1000000000) (929379 / 250000) (464719 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43099 / 512000) (43107 / 512000) (929379 / 250000) (464719 / 125000) (32973 / 1000) (16491 / 500)
    (26059 / 500) (26127 / 500) (-556297 / 1000) (378753 / 1000000) (1528311 / 500) (367071 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (929379 / 250000) (1743532101 / 25000) (367071 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (929379 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (929379 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell628 :
    ∀ t ∈ Set.Icc ((43107 / 512000) : ℝ) (8623 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((591697081 / 500000000) : ℝ) ≤ Real.exp (2 * (43107 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43107 / 512000)) (591697081 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8623 / 102400) : ℝ)) ≤ (236686229 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8623 / 102400)) (236686229 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((34882779109 / 500000) : ℝ) ≤ Real.exp (3 * (58088 / 15625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (58088 / 15625)) (34882779109 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43107 / 512000) : ℝ) (8623 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (58088 / 15625) (929467 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43107 / 512000) (8623 / 102400) (591697081 / 500000000) (236686229 / 200000000) (58088 / 15625) (929467 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43107 / 512000) (8623 / 102400) (58088 / 15625) (929467 / 250000) (1319 / 40) (6597 / 200)
    (52133 / 1000) (13067 / 250) (-139079 / 250) (11833 / 31250) (3057003 / 1000) (3669433 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (58088 / 15625) (34882779109 / 500000) (3669433 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (58088 / 15625)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (58088 / 15625)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell629 :
    ∀ t ∈ Set.Icc ((8623 / 102400) : ℝ) (43123 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((147928893 / 125000000) : ℝ) ≤ Real.exp (2 * (8623 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8623 / 102400)) (147928893 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43123 / 512000) : ℝ)) ≤ (36983379 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43123 / 512000)) (36983379 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13957968169 / 200000) : ℝ) ≤ Real.exp (3 * (929437 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (929437 / 250000)) (13957968169 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8623 / 102400) : ℝ) (43123 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (929437 / 250000) (116187 / 31250) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8623 / 102400) (43123 / 512000) (147928893 / 125000000) (36983379 / 31250000) (929437 / 250000) (116187 / 31250) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8623 / 102400) (43123 / 512000) (929437 / 250000) (116187 / 31250) (16489 / 500) (8247 / 250)
    (52147 / 1000) (26141 / 500) (-111267 / 200) (1183 / 3125) (611477 / 200) (917039 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (929437 / 250000) (13957968169 / 200000) (917039 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (929437 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (929437 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell630 :
    ∀ t ∈ Set.Icc ((43123 / 512000) : ℝ) (43131 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1183468127 / 1000000000) : ℝ) ≤ Real.exp (2 * (43123 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43123 / 512000)) (1183468127 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43131 / 512000) : ℝ)) ≤ (147938139 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43131 / 512000)) (147938139 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((34907170683 / 500000) : ℝ) ≤ Real.exp (3 * (743573 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (743573 / 200000)) (34907170683 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43123 / 512000) : ℝ) (43131 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (743573 / 200000) (37181 / 10000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43123 / 512000) (43131 / 512000) (1183468127 / 1000000000) (147938139 / 125000000) (743573 / 200000) (37181 / 10000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43123 / 512000) (43131 / 512000) (743573 / 200000) (37181 / 10000) (32981 / 1000) (3299 / 100)
    (26081 / 500) (6537 / 125) (-556359 / 1000) (378463 / 1000000) (1528883 / 500) (3666869 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (743573 / 200000) (34907170683 / 500000) (3666869 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (743573 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (743573 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell631 :
    ∀ t ∈ Set.Icc ((43131 / 512000) : ℝ) (43139 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1183505111 / 1000000000) : ℝ) ≤ Real.exp (2 * (43131 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43131 / 512000)) (1183505111 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43139 / 512000) : ℝ)) ≤ (1183542097 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43139 / 512000)) (1183542097 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((17459660243 / 250000) : ℝ) ≤ Real.exp (3 * (3717981 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3717981 / 1000000)) (17459660243 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43131 / 512000) : ℝ) (43139 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3717981 / 1000000) (464777 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43131 / 512000) (43139 / 512000) (1183505111 / 1000000000) (1183542097 / 1000000000) (3717981 / 1000000) (464777 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43131 / 512000) (43139 / 512000) (3717981 / 1000000) (464777 / 125000) (4123 / 125) (32993 / 1000)
    (6522 / 125) (52311 / 1000) (-278189 / 500) (189183 / 500000) (764537 / 250) (3665593 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3717981 / 1000000) (17459660243 / 250000) (3665593 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3717981 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3717981 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell632 :
    ∀ t ∈ Set.Icc ((43139 / 512000) : ℝ) (43147 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((73971381 / 62500000) : ℝ) ≤ Real.exp (2 * (43139 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43139 / 512000)) (73971381 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43147 / 512000) : ℝ)) ≤ (1183579083 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43147 / 512000)) (1183579083 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((17465737259 / 250000) : ℝ) ≤ Real.exp (3 * (3718097 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3718097 / 1000000)) (17465737259 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43139 / 512000) : ℝ) (43147 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3718097 / 1000000) (3718333 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43139 / 512000) (43147 / 512000) (73971381 / 62500000) (1183579083 / 1000000000) (3718097 / 1000000) (3718333 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43139 / 512000) (43147 / 512000) (3718097 / 1000000) (3718333 / 1000000) (16493 / 500) (8249 / 250)
    (5219 / 100) (26163 / 500) (-556393 / 1000) (37827 / 100000) (3058533 / 1000) (1832159 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3718097 / 1000000) (17465737259 / 250000) (1832159 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3718097 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3718097 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell633 :
    ∀ t ∈ Set.Icc ((43147 / 512000) : ℝ) (8631 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((591789541 / 500000000) : ℝ) ≤ Real.exp (2 * (43147 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43147 / 512000)) (591789541 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8631 / 102400) : ℝ)) ≤ (1183616071 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8631 / 102400)) (1183616071 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((69887265561 / 1000000) : ℝ) ≤ Real.exp (3 * (3718213 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3718213 / 1000000)) (69887265561 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43147 / 512000) : ℝ) (8631 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3718213 / 1000000) (3718449 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43147 / 512000) (8631 / 102400) (591789541 / 500000000) (1183616071 / 1000000000) (3718213 / 1000000) (3718449 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43147 / 512000) (8631 / 102400) (3718213 / 1000000) (3718449 / 1000000) (32989 / 1000) (32999 / 1000)
    (13051 / 250) (2617 / 50) (-139103 / 250) (189087 / 500000) (611783 / 200) (3663043 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3718213 / 1000000) (69887265561 / 1000000) (3663043 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3718213 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3718213 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell634 :
    ∀ t ∈ Set.Icc ((8631 / 102400) : ℝ) (43163 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((118361607 / 100000000) : ℝ) ≤ Real.exp (2 * (8631 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8631 / 102400)) (118361607 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43163 / 512000) : ℝ)) ≤ (1183653059 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43163 / 512000)) (1183653059 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((69911590549 / 1000000) : ℝ) ≤ Real.exp (3 * (3718329 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3718329 / 1000000)) (69911590549 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8631 / 102400) : ℝ) (43163 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3718329 / 1000000) (743713 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8631 / 102400) (43163 / 512000) (118361607 / 100000000) (1183653059 / 1000000000) (3718329 / 1000000) (743713 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8631 / 102400) (43163 / 512000) (3718329 / 1000000) (743713 / 200000) (4124 / 125) (33001 / 1000)
    (52219 / 1000) (26177 / 500) (-556431 / 1000) (189039 / 500000) (382412 / 125) (457721 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3718329 / 1000000) (69911590549 / 1000000) (457721 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3718329 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3718329 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell635 :
    ∀ t ∈ Set.Icc ((43163 / 512000) : ℝ) (43171 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((591826529 / 500000000) : ℝ) ≤ Real.exp (2 * (43163 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43163 / 512000)) (591826529 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43171 / 512000) : ℝ)) ≤ (1183690049 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43171 / 512000)) (1183690049 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((69936133811 / 1000000) : ℝ) ≤ Real.exp (3 * (1859223 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1859223 / 500000)) (69936133811 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43163 / 512000) : ℝ) (43171 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1859223 / 500000) (3718681 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43163 / 512000) (43171 / 512000) (591826529 / 500000000) (1183690049 / 1000000000) (1859223 / 500000) (3718681 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43163 / 512000) (43171 / 512000) (1859223 / 500000) (3718681 / 1000000) (6599 / 200) (8251 / 250)
    (52233 / 1000) (6546 / 125) (-111291 / 200) (377981 / 1000000) (1529839 / 500) (3660483 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1859223 / 500000) (69936133811 / 1000000) (3660483 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1859223 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1859223 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell636 :
    ∀ t ∈ Set.Icc ((43171 / 512000) : ℝ) (43179 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((18495157 / 15625000) : ℝ) ≤ Real.exp (2 * (43171 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43171 / 512000)) (18495157 / 15625000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43179 / 512000) : ℝ)) ≤ (3699147 / 3125000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43179 / 512000)) (3699147 / 3125000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((69960475809 / 1000000) : ℝ) ≤ Real.exp (3 * (1859281 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1859281 / 500000)) (69960475809 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43171 / 512000) : ℝ) (43179 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1859281 / 500000) (3718797 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43171 / 512000) (43179 / 512000) (18495157 / 15625000) (3699147 / 3125000) (1859281 / 500000) (3718797 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43171 / 512000) (43179 / 512000) (1859281 / 500000) (3718797 / 1000000) (16499 / 500) (33007 / 1000)
    (6531 / 125) (52383 / 1000) (-278237 / 500) (94471 / 250000) (153003 / 50) (3659209 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1859281 / 500000) (69960475809 / 1000000) (3659209 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1859281 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1859281 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell637 :
    ∀ t ∈ Set.Icc ((43179 / 512000) : ℝ) (43187 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1183727039 / 1000000000) : ℝ) ≤ Real.exp (2 * (43179 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43179 / 512000)) (1183727039 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43187 / 512000) : ℝ)) ≤ (18496313 / 15625000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43187 / 512000)) (18496313 / 15625000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((34992413139 / 500000) : ℝ) ≤ Real.exp (3 * (1859339 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1859339 / 500000)) (34992413139 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43179 / 512000) : ℝ) (43187 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1859339 / 500000) (1859457 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43179 / 512000) (43187 / 512000) (1183727039 / 1000000000) (18496313 / 15625000) (1859339 / 500000) (1859457 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43179 / 512000) (43187 / 512000) (1859339 / 500000) (1859457 / 500000) (33) (3301 / 100)
    (26131 / 500) (52397 / 1000) (-556489 / 1000) (377789 / 1000000) (612089 / 200) (228621 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1859339 / 500000) (34992413139 / 500000) (228621 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1859339 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1859339 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell638 :
    ∀ t ∈ Set.Icc ((43187 / 512000) : ℝ) (8639 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1183764031 / 1000000000) : ℝ) ≤ Real.exp (2 * (43187 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43187 / 512000)) (1183764031 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8639 / 102400) : ℝ)) ≤ (47352041 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8639 / 102400)) (47352041 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8751148153 / 125000) : ℝ) ≤ Real.exp (3 * (1859397 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1859397 / 500000)) (8751148153 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43187 / 512000) : ℝ) (8639 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1859397 / 500000) (371903 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43187 / 512000) (8639 / 102400) (1183764031 / 1000000000) (47352041 / 40000000) (1859397 / 500000) (371903 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43187 / 512000) (8639 / 102400) (1859397 / 500000) (371903 / 100000) (33003 / 1000) (8253 / 250)
    (13069 / 250) (13103 / 250) (-139127 / 250) (377693 / 1000000) (3060827 / 1000) (457083 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1859397 / 500000) (8751148153 / 125000) (457083 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1859397 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1859397 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell639 :
    ∀ t ∈ Set.Icc ((8639 / 102400) : ℝ) (43203 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((18496891 / 15625000) : ℝ) ≤ Real.exp (2 * (8639 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8639 / 102400)) (18496891 / 15625000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43203 / 512000) : ℝ)) ≤ (1183838019 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43203 / 512000)) (1183838019 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((70033552647 / 1000000) : ℝ) ≤ Real.exp (3 * (371891 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (371891 / 100000)) (70033552647 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8639 / 102400) : ℝ) (43203 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (371891 / 100000) (1859573 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8639 / 102400) (43203 / 512000) (18496891 / 15625000) (1183838019 / 1000000000) (371891 / 100000) (1859573 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8639 / 102400) (43203 / 512000) (371891 / 100000) (1859573 / 500000) (16503 / 500) (6603 / 200)
    (52291 / 1000) (26213 / 500) (-556527 / 1000) (94399 / 250000) (3061209 / 1000) (3655391 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (371891 / 100000) (70033552647 / 1000000) (3655391 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (371891 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (371891 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch031 :
    ∀ t ∈ Set.Icc ((43043 / 512000) : ℝ) (43203 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell620
      hpThetaDensityLowerExpCompact_cell621)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell622
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell623
      hpThetaDensityLowerExpCompact_cell624)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell625
      hpThetaDensityLowerExpCompact_cell626)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell627
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell628
      hpThetaDensityLowerExpCompact_cell629))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell630
      hpThetaDensityLowerExpCompact_cell631)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell632
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell633
      hpThetaDensityLowerExpCompact_cell634)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell635
      hpThetaDensityLowerExpCompact_cell636)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell637
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell638
      hpThetaDensityLowerExpCompact_cell639)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch031
end HodgeProofHP
