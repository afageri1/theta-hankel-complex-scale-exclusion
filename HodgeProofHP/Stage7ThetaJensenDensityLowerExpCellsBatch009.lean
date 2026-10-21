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
theorem hpThetaDensityLowerExpCompact_cell180 :
    ∀ t ∈ Set.Icc ((41167 / 512000) : ℝ) (41169 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293615037 / 250000000) : ℝ) ≤ Real.exp (2 * (41167 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41167 / 512000)) (293615037 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41169 / 512000) : ℝ)) ≤ (293617331 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41169 / 512000)) (293617331 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64131938017 / 1000000) : ℝ) ≤ Real.exp (3 * (1844783 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1844783 / 500000)) (64131938017 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41167 / 512000) : ℝ) (41169 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1844783 / 500000) (3689713 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41167 / 512000) (41169 / 512000) (293615037 / 250000000) (293617331 / 250000000) (1844783 / 500000) (3689713 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41167 / 512000) (41169 / 512000) (1844783 / 500000) (3689713 / 1000000) (32313 / 1000) (32319 / 1000)
    (48729 / 1000) (48813 / 1000) (-13797 / 25) (402631 / 1000000) (2965449 / 1000) (3991771 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1844783 / 500000) (64131938017 / 1000000) (3991771 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844783 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844783 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell181 :
    ∀ t ∈ Set.Icc ((41169 / 512000) : ℝ) (41171 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174469323 / 1000000000) : ℝ) ≤ Real.exp (2 * (41169 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41169 / 512000)) (1174469323 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41171 / 512000) : ℝ)) ≤ (2348957 / 2000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41171 / 512000)) (2348957 / 2000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8017189717 / 125000) : ℝ) ≤ Real.exp (3 * (737919 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (737919 / 200000)) (8017189717 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41169 / 512000) : ℝ) (41171 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (737919 / 200000) (1844871 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41169 / 512000) (41171 / 512000) (1174469323 / 1000000000) (2348957 / 2000000) (737919 / 200000) (1844871 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41169 / 512000) (41171 / 512000) (737919 / 200000) (1844871 / 500000) (32313 / 1000) (808 / 25)
    (12183 / 250) (6102 / 125) (-110377 / 200) (201303 / 500000) (1482771 / 500) (31183 / 7812500)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (737919 / 200000) (8017189717 / 125000) (31183 / 7812500)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (737919 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (737919 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell182 :
    ∀ t ∈ Set.Icc ((41171 / 512000) : ℝ) (41173 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174478499 / 1000000000) : ℝ) ≤ Real.exp (2 * (41171 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41171 / 512000)) (1174478499 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41173 / 512000) : ℝ)) ≤ (293621919 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41173 / 512000)) (293621919 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3207154897 / 50000) : ℝ) ≤ Real.exp (3 * (461203 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (461203 / 125000)) (3207154897 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41171 / 512000) : ℝ) (41173 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (461203 / 125000) (3689771 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41171 / 512000) (41173 / 512000) (1174478499 / 1000000000) (293621919 / 250000000) (461203 / 125000) (3689771 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41171 / 512000) (41173 / 512000) (461203 / 125000) (3689771 / 1000000) (16157 / 500) (808 / 25)
    (6092 / 125) (2441 / 50) (-55189 / 100) (20129 / 50000) (593127 / 200) (3991077 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (461203 / 125000) (3207154897 / 50000) (3991077 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461203 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461203 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell183 :
    ∀ t ∈ Set.Icc ((41173 / 512000) : ℝ) (1647 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((46979507 / 40000000) : ℝ) ≤ Real.exp (2 * (41173 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41173 / 512000)) (46979507 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1647 / 20480) : ℝ)) ≤ (1174496851 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1647 / 20480)) (1174496851 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6414867863 / 100000) : ℝ) ≤ Real.exp (3 * (3689653 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3689653 / 1000000)) (6414867863 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41173 / 512000) : ℝ) (1647 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3689653 / 1000000) (18449 / 5000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41173 / 512000) (1647 / 20480) (46979507 / 40000000) (1174496851 / 1000000000) (3689653 / 1000000) (18449 / 5000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41173 / 512000) (1647 / 20480) (3689653 / 1000000) (18449 / 5000) (6463 / 200) (32321 / 1000)
    (48739 / 1000) (48823 / 1000) (-110379 / 200) (80511 / 200000) (370716 / 125) (399073 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3689653 / 1000000) (6414867863 / 100000) (399073 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689653 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689653 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell184 :
    ∀ t ∈ Set.Icc ((1647 / 20480) : ℝ) (41177 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((23489937 / 20000000) : ℝ) ≤ Real.exp (2 * (1647 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1647 / 20480)) (23489937 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41177 / 512000) : ℝ)) ≤ (1174506027 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41177 / 512000)) (1174506027 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64154067343 / 1000000) : ℝ) ≤ Real.exp (3 * (3689681 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3689681 / 1000000)) (64154067343 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1647 / 20480) : ℝ) (41177 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3689681 / 1000000) (3689829 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1647 / 20480) (41177 / 512000) (23489937 / 20000000) (1174506027 / 1000000000) (3689681 / 1000000) (3689829 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1647 / 20480) (41177 / 512000) (3689681 / 1000000) (3689829 / 1000000) (8079 / 250) (16161 / 500)
    (48743 / 1000) (48827 / 1000) (-68987 / 125) (40253 / 100000) (1482911 / 500) (1995197 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3689681 / 1000000) (64154067343 / 1000000) (1995197 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689681 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689681 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell185 :
    ∀ t ∈ Set.Icc ((41177 / 512000) : ℝ) (41179 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587253013 / 500000000) : ℝ) ≤ Real.exp (2 * (41177 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41177 / 512000)) (587253013 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41179 / 512000) : ℝ)) ≤ (1174515203 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41179 / 512000)) (1174515203 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64159648987 / 1000000) : ℝ) ≤ Real.exp (3 * (368971 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (368971 / 100000)) (64159648987 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41177 / 512000) : ℝ) (41179 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (368971 / 100000) (3689857 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41177 / 512000) (41179 / 512000) (587253013 / 500000000) (1174515203 / 1000000000) (368971 / 100000) (3689857 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41177 / 512000) (41179 / 512000) (368971 / 100000) (3689857 / 1000000) (8079 / 250) (16161 / 500)
    (24373 / 500) (4883 / 100) (-110381 / 200) (80501 / 200000) (370739 / 125) (3990047 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (368971 / 100000) (64159648987 / 1000000) (3990047 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (368971 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (368971 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell186 :
    ∀ t ∈ Set.Icc ((41179 / 512000) : ℝ) (41181 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587257601 / 500000000) : ℝ) ≤ Real.exp (2 * (41179 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41179 / 512000)) (587257601 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41181 / 512000) : ℝ)) ≤ (1174524379 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41181 / 512000)) (1174524379 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64165231117 / 1000000) : ℝ) ≤ Real.exp (3 * (3689739 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3689739 / 1000000)) (64165231117 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41179 / 512000) : ℝ) (41181 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3689739 / 1000000) (1844943 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41179 / 512000) (41181 / 512000) (587257601 / 500000000) (1174524379 / 1000000000) (3689739 / 1000000) (1844943 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41179 / 512000) (41181 / 512000) (3689739 / 1000000) (1844943 / 500000) (32317 / 1000) (32323 / 1000)
    (195 / 4) (24417 / 500) (-551911 / 1000) (402479 / 1000000) (593201 / 200) (39897 / 10000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3689739 / 1000000) (64165231117 / 1000000) (39897 / 10000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689739 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689739 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell187 :
    ∀ t ∈ Set.Icc ((41181 / 512000) : ℝ) (41183 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587262189 / 500000000) : ℝ) ≤ Real.exp (2 * (41181 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41181 / 512000)) (587262189 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41183 / 512000) : ℝ)) ≤ (234906711 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41183 / 512000)) (234906711 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64170813733 / 1000000) : ℝ) ≤ Real.exp (3 * (461221 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (461221 / 125000)) (64170813733 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41181 / 512000) : ℝ) (41183 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (461221 / 125000) (737983 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41181 / 512000) (41183 / 512000) (587262189 / 500000000) (234906711 / 200000000) (461221 / 125000) (737983 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41181 / 512000) (41183 / 512000) (461221 / 125000) (737983 / 200000) (16159 / 500) (8081 / 250)
    (48753 / 1000) (48837 / 1000) (-137979 / 250) (201227 / 500000) (1483049 / 500) (3989353 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (461221 / 125000) (64170813733 / 1000000) (3989353 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461221 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461221 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell188 :
    ∀ t ∈ Set.Icc ((41183 / 512000) : ℝ) (8237 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587266777 / 500000000) : ℝ) ≤ Real.exp (2 * (41183 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41183 / 512000)) (587266777 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8237 / 102400) : ℝ)) ≤ (1174542731 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8237 / 102400)) (1174542731 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32088198417 / 500000) : ℝ) ≤ Real.exp (3 * (3689797 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3689797 / 1000000)) (32088198417 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41183 / 512000) : ℝ) (8237 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3689797 / 1000000) (461243 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41183 / 512000) (8237 / 102400) (587266777 / 500000000) (1174542731 / 1000000000) (3689797 / 1000000) (461243 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41183 / 512000) (8237 / 102400) (3689797 / 1000000) (461243 / 125000) (16159 / 500) (8081 / 250)
    (48757 / 1000) (48841 / 1000) (-551921 / 1000) (100607 / 250000) (2966191 / 1000) (1994503 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3689797 / 1000000) (32088198417 / 500000) (1994503 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689797 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689797 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell189 :
    ∀ t ∈ Set.Icc ((8237 / 102400) : ℝ) (41187 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((117454273 / 100000000) : ℝ) ≤ Real.exp (2 * (8237 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8237 / 102400)) (117454273 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41187 / 512000) : ℝ)) ≤ (1174551907 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41187 / 512000)) (1174551907 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((513454303 / 8000) : ℝ) ≤ Real.exp (3 * (147593 / 40000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (147593 / 40000)) (513454303 / 8000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8237 / 102400) : ℝ) (41187 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (147593 / 40000) (3689973 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8237 / 102400) (41187 / 512000) (117454273 / 100000000) (1174551907 / 1000000000) (147593 / 40000) (3689973 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8237 / 102400) (41187 / 512000) (147593 / 40000) (3689973 / 1000000) (32319 / 1000) (1293 / 40)
    (1219 / 25) (12211 / 250) (-551921 / 1000) (100601 / 250000) (593257 / 200) (3988671 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (147593 / 40000) (513454303 / 8000) (3988671 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (147593 / 40000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (147593 / 40000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell190 :
    ∀ t ∈ Set.Icc ((41187 / 512000) : ℝ) (41189 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587275953 / 500000000) : ℝ) ≤ Real.exp (2 * (41187 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41187 / 512000)) (587275953 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41189 / 512000) : ℝ)) ≤ (1174561083 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41189 / 512000)) (1174561083 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64187371931 / 1000000) : ℝ) ≤ Real.exp (3 * (1844927 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1844927 / 500000)) (64187371931 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41187 / 512000) : ℝ) (41189 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1844927 / 500000) (1845001 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41187 / 512000) (41189 / 512000) (587275953 / 500000000) (1174561083 / 1000000000) (1844927 / 500000) (1845001 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41187 / 512000) (41189 / 512000) (1844927 / 500000) (1845001 / 500000) (808 / 25) (16163 / 500)
    (48763 / 1000) (6106 / 125) (-551927 / 1000) (201189 / 500000) (1483189 / 500) (997081 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1844927 / 500000) (64187371931 / 1000000) (997081 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844927 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844927 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell191 :
    ∀ t ∈ Set.Icc ((41189 / 512000) : ℝ) (41191 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587280541 / 500000000) : ℝ) ≤ Real.exp (2 * (41189 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41189 / 512000)) (587280541 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41191 / 512000) : ℝ)) ≤ (58728513 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41191 / 512000)) (58728513 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64192956473 / 1000000) : ℝ) ≤ Real.exp (3 * (3689883 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3689883 / 1000000)) (64192956473 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41189 / 512000) : ℝ) (41191 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3689883 / 1000000) (369003 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41189 / 512000) (41191 / 512000) (587280541 / 500000000) (58728513 / 50000000) (3689883 / 1000000) (369003 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41189 / 512000) (41191 / 512000) (3689883 / 1000000) (369003 / 100000) (808 / 25) (16163 / 500)
    (48767 / 1000) (48851 / 1000) (-68992 / 125) (25147 / 62500) (741617 / 250) (3987977 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3689883 / 1000000) (64192956473 / 1000000) (3987977 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689883 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689883 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell192 :
    ∀ t ∈ Set.Icc ((41191 / 512000) : ℝ) (41193 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174570259 / 1000000000) : ℝ) ≤ Real.exp (2 * (41191 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41191 / 512000)) (1174570259 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41193 / 512000) : ℝ)) ≤ (293644859 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41193 / 512000)) (293644859 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64198541501 / 1000000) : ℝ) ≤ Real.exp (3 * (461239 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (461239 / 125000)) (64198541501 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41191 / 512000) : ℝ) (41193 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (461239 / 125000) (3690059 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41191 / 512000) (41193 / 512000) (1174570259 / 1000000000) (293644859 / 250000000) (461239 / 125000) (3690059 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41191 / 512000) (41193 / 512000) (461239 / 125000) (3690059 / 1000000) (32321 / 1000) (32327 / 1000)
    (48771 / 1000) (24427 / 500) (-551941 / 1000) (402327 / 1000000) (2966561 / 1000) (398763 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (461239 / 125000) (64198541501 / 1000000) (398763 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461239 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461239 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell193 :
    ∀ t ∈ Set.Icc ((41193 / 512000) : ℝ) (8239 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((234915887 / 200000000) : ℝ) ≤ Real.exp (2 * (41193 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41193 / 512000)) (234915887 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8239 / 102400) : ℝ)) ≤ (293647153 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8239 / 102400)) (293647153 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32102063507 / 500000) : ℝ) ≤ Real.exp (3 * (3689941 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3689941 / 1000000)) (32102063507 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41193 / 512000) : ℝ) (8239 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3689941 / 1000000) (461261 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41193 / 512000) (8239 / 102400) (234915887 / 200000000) (293647153 / 250000000) (3689941 / 1000000) (461261 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41193 / 512000) (8239 / 102400) (3689941 / 1000000) (461261 / 125000) (16161 / 500) (4041 / 125)
    (24387 / 500) (24429 / 500) (-551947 / 1000) (402301 / 1000000) (1483327 / 500) (3987283 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3689941 / 1000000) (32102063507 / 500000) (3987283 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689941 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3689941 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell194 :
    ∀ t ∈ Set.Icc ((8239 / 102400) : ℝ) (41197 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174588611 / 1000000000) : ℝ) ≤ Real.exp (2 * (8239 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8239 / 102400)) (1174588611 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41197 / 512000) : ℝ)) ≤ (1174597789 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41197 / 512000)) (1174597789 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32104856507 / 500000) : ℝ) ≤ Real.exp (3 * (368997 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (368997 / 100000)) (32104856507 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8239 / 102400) : ℝ) (41197 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (368997 / 100000) (3690117 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8239 / 102400) (41197 / 512000) (1174588611 / 1000000000) (1174597789 / 1000000000) (368997 / 100000) (3690117 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8239 / 102400) (41197 / 512000) (368997 / 100000) (3690117 / 1000000) (16161 / 500) (32329 / 1000)
    (24389 / 500) (48861 / 1000) (-68994 / 125) (100569 / 250000) (741687 / 250) (498367 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (368997 / 100000) (32104856507 / 500000) (498367 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (368997 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (368997 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell195 :
    ∀ t ∈ Set.Icc ((41197 / 512000) : ℝ) (41199 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293649447 / 250000000) : ℝ) ≤ Real.exp (2 * (41197 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41197 / 512000)) (293649447 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41199 / 512000) : ℝ)) ≤ (234921393 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41199 / 512000)) (234921393 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32107553427 / 500000) : ℝ) ≤ Real.exp (3 * (1844999 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1844999 / 500000)) (32107553427 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41197 / 512000) : ℝ) (41199 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1844999 / 500000) (1845073 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41197 / 512000) (41199 / 512000) (293649447 / 250000000) (234921393 / 200000000) (1844999 / 500000) (1845073 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41197 / 512000) (41199 / 512000) (1844999 / 500000) (1845073 / 500000) (32323 / 1000) (32329 / 1000)
    (48781 / 1000) (9773 / 200) (-68994 / 125) (402251 / 1000000) (2966841 / 1000) (3986601 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1844999 / 500000) (32107553427 / 500000) (3986601 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844999 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844999 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell196 :
    ∀ t ∈ Set.Icc ((41199 / 512000) : ℝ) (41201 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293651741 / 250000000) : ℝ) ≤ Real.exp (2 * (41199 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41199 / 512000)) (293651741 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41201 / 512000) : ℝ)) ≤ (587308071 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41201 / 512000)) (587308071 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64220693809 / 1000000) : ℝ) ≤ Real.exp (3 * (3690027 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3690027 / 1000000)) (64220693809 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41199 / 512000) : ℝ) (41201 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3690027 / 1000000) (147607 / 40000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41199 / 512000) (41201 / 512000) (293651741 / 250000000) (587308071 / 500000000) (3690027 / 1000000) (147607 / 40000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41199 / 512000) (41201 / 512000) (3690027 / 1000000) (147607 / 40000) (8081 / 250) (3233 / 100)
    (6098 / 125) (48869 / 1000) (-275979 / 500) (201113 / 500000) (1483467 / 500) (797251 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3690027 / 1000000) (64220693809 / 1000000) (797251 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690027 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690027 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell197 :
    ∀ t ∈ Set.Icc ((41201 / 512000) : ℝ) (41203 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174616141 / 1000000000) : ℝ) ≤ Real.exp (2 * (41201 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41201 / 512000)) (1174616141 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41203 / 512000) : ℝ)) ≤ (1174625319 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41203 / 512000)) (1174625319 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2055241 / 32) : ℝ) ≤ Real.exp (3 * (461257 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (461257 / 125000)) (2055241 / 32) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41201 / 512000) : ℝ) (41203 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (461257 / 125000) (3690203 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41201 / 512000) (41203 / 512000) (1174616141 / 1000000000) (1174625319 / 1000000000) (461257 / 125000) (3690203 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41201 / 512000) (41203 / 512000) (461257 / 125000) (3690203 / 1000000) (8081 / 250) (32331 / 1000)
    (12197 / 250) (6109 / 125) (-551967 / 1000) (2011 / 5000) (370878 / 125) (996477 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (461257 / 125000) (2055241 / 32) (996477 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461257 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461257 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell198 :
    ∀ t ∈ Set.Icc ((41203 / 512000) : ℝ) (8241 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587312659 / 500000000) : ℝ) ≤ Real.exp (2 * (41203 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41203 / 512000)) (587312659 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8241 / 102400) : ℝ)) ≤ (2294208 / 1953125) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8241 / 102400)) (2294208 / 1953125) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64231869177 / 1000000) : ℝ) ≤ Real.exp (3 * (738017 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (738017 / 200000)) (64231869177 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41203 / 512000) : ℝ) (8241 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (738017 / 200000) (461279 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41203 / 512000) (8241 / 102400) (587312659 / 500000000) (2294208 / 1953125) (738017 / 200000) (461279 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41203 / 512000) (8241 / 102400) (738017 / 200000) (461279 / 125000) (1293 / 40) (32331 / 1000)
    (48791 / 1000) (391 / 8) (-137993 / 250) (16087 / 40000) (2967117 / 1000) (3985561 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (738017 / 200000) (64231869177 / 1000000) (3985561 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (738017 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (738017 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell199 :
    ∀ t ∈ Set.Icc ((8241 / 102400) : ℝ) (41207 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((234926899 / 200000000) : ℝ) ≤ Real.exp (2 * (8241 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8241 / 102400)) (234926899 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41207 / 512000) : ℝ)) ≤ (1174643673 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41207 / 512000)) (1174643673 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6423745759 / 100000) : ℝ) ≤ Real.exp (3 * (1845057 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1845057 / 500000)) (6423745759 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8241 / 102400) : ℝ) (41207 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1845057 / 500000) (3690261 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8241 / 102400) (41207 / 512000) (234926899 / 200000000) (1174643673 / 1000000000) (1845057 / 500000) (3690261 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8241 / 102400) (41207 / 512000) (1845057 / 500000) (3690261 / 1000000) (16163 / 500) (8083 / 250)
    (9759 / 200) (48879 / 1000) (-275989 / 500) (402149 / 1000000) (2967211 / 1000) (1992607 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1845057 / 500000) (6423745759 / 100000) (1992607 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1845057 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1845057 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch009 :
    ∀ t ∈ Set.Icc ((41167 / 512000) : ℝ) (41207 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell180
      hpThetaDensityLowerExpCompact_cell181)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell182
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell183
      hpThetaDensityLowerExpCompact_cell184)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell185
      hpThetaDensityLowerExpCompact_cell186)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell187
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell188
      hpThetaDensityLowerExpCompact_cell189))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell190
      hpThetaDensityLowerExpCompact_cell191)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell192
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell193
      hpThetaDensityLowerExpCompact_cell194)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell195
      hpThetaDensityLowerExpCompact_cell196)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell197
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell198
      hpThetaDensityLowerExpCompact_cell199)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch009
end HodgeProofHP
