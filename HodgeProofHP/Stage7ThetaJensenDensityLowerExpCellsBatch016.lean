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
theorem hpThetaDensityLowerExpCompact_cell320 :
    ∀ t ∈ Set.Icc ((41447 / 512000) : ℝ) (41449 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((146968177 / 125000000) : ℝ) ≤ Real.exp (2 * (41447 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41447 / 512000)) (146968177 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41449 / 512000) : ℝ)) ≤ (1175754603 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41449 / 512000)) (1175754603 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64913556671 / 1000000) : ℝ) ≤ Real.exp (3 * (923401 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (923401 / 250000)) (64913556671 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41447 / 512000) : ℝ) (41449 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (923401 / 250000) (3693751 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41447 / 512000) (41449 / 512000) (146968177 / 125000000) (1175754603 / 1000000000) (923401 / 250000) (3693751 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41447 / 512000) (41449 / 512000) (923401 / 250000) (3693751 / 1000000) (4051 / 125) (16207 / 500)
    (6152 / 125) (493 / 10) (-552599 / 1000) (399091 / 1000000) (2978451 / 1000) (3943707 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (923401 / 250000) (64913556671 / 1000000) (3943707 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (923401 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (923401 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell321 :
    ∀ t ∈ Set.Icc ((41449 / 512000) : ℝ) (41451 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587877301 / 500000000) : ℝ) ≤ Real.exp (2 * (41449 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41449 / 512000)) (587877301 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41451 / 512000) : ℝ)) ≤ (293940947 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41451 / 512000)) (293940947 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32459602197 / 500000) : ℝ) ≤ Real.exp (3 * (3693633 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3693633 / 1000000)) (32459602197 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41449 / 512000) : ℝ) (41451 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3693633 / 1000000) (184689 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41449 / 512000) (41451 / 512000) (587877301 / 500000000) (293940947 / 250000000) (3693633 / 1000000) (184689 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41449 / 512000) (41451 / 512000) (3693633 / 1000000) (184689 / 50000) (32409 / 1000) (6483 / 200)
    (49219 / 1000) (49303 / 1000) (-138151 / 250) (199533 / 500000) (595709 / 200) (985841 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3693633 / 1000000) (32459602197 / 500000) (985841 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693633 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693633 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell322 :
    ∀ t ∈ Set.Icc ((41451 / 512000) : ℝ) (41453 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175763787 / 1000000000) : ℝ) ≤ Real.exp (2 * (41451 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41451 / 512000)) (1175763787 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41453 / 512000) : ℝ)) ≤ (587886487 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41453 / 512000)) (587886487 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32462328917 / 500000) : ℝ) ≤ Real.exp (3 * (3693661 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3693661 / 1000000)) (32462328917 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41451 / 512000) : ℝ) (41453 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3693661 / 1000000) (3693809 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41451 / 512000) (41453 / 512000) (1175763787 / 1000000000) (587886487 / 500000000) (3693661 / 1000000) (3693809 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41451 / 512000) (41453 / 512000) (3693661 / 1000000) (3693809 / 1000000) (32409 / 1000) (6483 / 200)
    (24611 / 500) (49307 / 1000) (-138151 / 250) (399041 / 1000000) (1489319 / 500) (492879 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3693661 / 1000000) (32462328917 / 500000) (492879 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693661 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693661 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell323 :
    ∀ t ∈ Set.Icc ((41453 / 512000) : ℝ) (8291 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175772973 / 1000000000) : ℝ) ≤ Real.exp (2 * (41453 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41453 / 512000)) (1175772973 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8291 / 102400) : ℝ)) ≤ (14697277 / 12500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8291 / 102400)) (14697277 / 12500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32465153261 / 500000) : ℝ) ≤ Real.exp (3 * (369369 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (369369 / 100000)) (32465153261 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41453 / 512000) : ℝ) (8291 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (369369 / 100000) (1846919 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41453 / 512000) (8291 / 102400) (1175772973 / 1000000000) (14697277 / 12500000) (369369 / 100000) (1846919 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41453 / 512000) (8291 / 102400) (369369 / 100000) (1846919 / 500000) (3241 / 100) (4052 / 125)
    (24613 / 500) (4931 / 100) (-552609 / 1000) (49877 / 125000) (744683 / 250) (3942689 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (369369 / 100000) (32465153261 / 500000) (3942689 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (369369 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (369369 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell324 :
    ∀ t ∈ Set.Icc ((8291 / 102400) : ℝ) (41457 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175782159 / 1000000000) : ℝ) ≤ Real.exp (2 * (8291 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8291 / 102400)) (1175782159 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41457 / 512000) : ℝ)) ≤ (587895673 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41457 / 512000)) (587895673 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32467977851 / 500000) : ℝ) ≤ Real.exp (3 * (3693719 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3693719 / 1000000)) (32467977851 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8291 / 102400) : ℝ) (41457 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3693719 / 1000000) (3693867 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8291 / 102400) (41457 / 512000) (1175782159 / 1000000000) (587895673 / 500000000) (3693719 / 1000000) (3693867 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8291 / 102400) (41457 / 512000) (3693719 / 1000000) (3693867 / 1000000) (32411 / 1000) (32417 / 1000)
    (49229 / 1000) (24657 / 500) (-110523 / 200) (398991 / 1000000) (1489413 / 500) (1971173 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3693719 / 1000000) (32467977851 / 500000) (1971173 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693719 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693719 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell325 :
    ∀ t ∈ Set.Icc ((41457 / 512000) : ℝ) (41459 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235158269 / 200000000) : ℝ) ≤ Real.exp (2 * (41457 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41457 / 512000)) (235158269 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41459 / 512000) : ℝ)) ≤ (293950133 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41459 / 512000)) (293950133 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64941605373 / 1000000) : ℝ) ≤ Real.exp (3 * (923437 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (923437 / 250000)) (64941605373 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41457 / 512000) : ℝ) (41459 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (923437 / 250000) (738779 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41457 / 512000) (41459 / 512000) (235158269 / 200000000) (293950133 / 250000000) (923437 / 250000) (738779 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41457 / 512000) (41459 / 512000) (923437 / 250000) (738779 / 200000) (32411 / 1000) (32417 / 1000)
    (49233 / 1000) (49317 / 1000) (-69078 / 125) (79793 / 200000) (744729 / 250) (3942003 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (923437 / 250000) (64941605373 / 1000000) (3942003 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (923437 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (923437 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell326 :
    ∀ t ∈ Set.Icc ((41459 / 512000) : ℝ) (41461 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175800531 / 1000000000) : ℝ) ≤ Real.exp (2 * (41459 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41459 / 512000)) (1175800531 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41461 / 512000) : ℝ)) ≤ (587904859 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41461 / 512000)) (587904859 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4059203471 / 62500) : ℝ) ≤ Real.exp (3 * (3693777 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3693777 / 1000000)) (4059203471 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41459 / 512000) : ℝ) (41461 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3693777 / 1000000) (923481 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41459 / 512000) (41461 / 512000) (1175800531 / 1000000000) (587904859 / 500000000) (3693777 / 1000000) (923481 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41459 / 512000) (41461 / 512000) (3693777 / 1000000) (923481 / 250000) (8103 / 250) (16209 / 500)
    (49237 / 1000) (49321 / 1000) (-552629 / 1000) (19947 / 50000) (2979009 / 1000) (3941661 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3693777 / 1000000) (4059203471 / 62500) (3941661 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693777 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693777 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell327 :
    ∀ t ∈ Set.Icc ((41461 / 512000) : ℝ) (41463 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175809717 / 1000000000) : ℝ) ≤ Real.exp (2 * (41461 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41461 / 512000)) (1175809717 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41463 / 512000) : ℝ)) ≤ (146977363 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41463 / 512000)) (146977363 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64952906191 / 1000000) : ℝ) ≤ Real.exp (3 * (1846903 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1846903 / 500000)) (64952906191 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41461 / 512000) : ℝ) (41463 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1846903 / 500000) (3693953 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41461 / 512000) (41463 / 512000) (1175809717 / 1000000000) (146977363 / 125000000) (1846903 / 500000) (3693953 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41461 / 512000) (41463 / 512000) (1846903 / 500000) (3693953 / 1000000) (32413 / 1000) (32419 / 1000)
    (1231 / 25) (12331 / 250) (-276317 / 500) (79783 / 200000) (2979103 / 1000) (1970659 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1846903 / 500000) (64952906191 / 1000000) (1970659 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1846903 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1846903 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell328 :
    ∀ t ∈ Set.Icc ((41463 / 512000) : ℝ) (8293 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175818903 / 1000000000) : ℝ) ≤ Real.exp (2 * (41463 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41463 / 512000)) (1175818903 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8293 / 102400) : ℝ)) ≤ (117582809 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8293 / 102400)) (117582809 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64958557337 / 1000000) : ℝ) ≤ Real.exp (3 * (738767 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (738767 / 200000)) (64958557337 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41463 / 512000) : ℝ) (8293 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (738767 / 200000) (1846991 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41463 / 512000) (8293 / 102400) (1175818903 / 1000000000) (117582809 / 100000000) (738767 / 200000) (1846991 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41463 / 512000) (8293 / 102400) (738767 / 200000) (1846991 / 500000) (32413 / 1000) (1621 / 50)
    (12311 / 250) (6166 / 125) (-552639 / 1000) (398889 / 1000000) (2979197 / 1000) (157639 / 40000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (738767 / 200000) (64958557337 / 1000000) (157639 / 40000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (738767 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (738767 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell329 :
    ∀ t ∈ Set.Icc ((8293 / 102400) : ℝ) (41467 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175828089 / 1000000000) : ℝ) ≤ Real.exp (2 * (8293 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8293 / 102400)) (1175828089 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41467 / 512000) : ℝ)) ≤ (293959319 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41467 / 512000)) (293959319 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32482007041 / 500000) : ℝ) ≤ Real.exp (3 * (3693863 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3693863 / 1000000)) (32482007041 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8293 / 102400) : ℝ) (41467 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3693863 / 1000000) (3694011 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8293 / 102400) (41467 / 512000) (1175828089 / 1000000000) (293959319 / 250000000) (3693863 / 1000000) (3694011 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8293 / 102400) (41467 / 512000) (3693863 / 1000000) (3694011 / 1000000) (16207 / 500) (1621 / 50)
    (49247 / 1000) (49331 / 1000) (-13816 / 25) (79773 / 200000) (297929 / 100) (985161 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3693863 / 1000000) (32482007041 / 500000) (985161 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693863 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693863 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell330 :
    ∀ t ∈ Set.Icc ((41467 / 512000) : ℝ) (41469 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((47033491 / 40000000) : ℝ) ≤ Real.exp (2 * (41467 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41467 / 512000)) (47033491 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41469 / 512000) : ℝ)) ≤ (587923231 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41469 / 512000)) (587923231 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((12993933239 / 200000) : ℝ) ≤ Real.exp (3 * (923473 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (923473 / 250000)) (12993933239 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41467 / 512000) : ℝ) (41469 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (923473 / 250000) (92351 / 25000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41467 / 512000) (41469 / 512000) (47033491 / 40000000) (587923231 / 500000000) (923473 / 250000) (92351 / 25000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41467 / 512000) (41469 / 512000) (923473 / 250000) (92351 / 25000) (6483 / 200) (32421 / 1000)
    (197 / 4) (9867 / 200) (-110529 / 200) (9971 / 25000) (372423 / 125) (3940301 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (923473 / 250000) (12993933239 / 200000) (3940301 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (923473 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (923473 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell331 :
    ∀ t ∈ Set.Icc ((41469 / 512000) : ℝ) (41473 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175846461 / 1000000000) : ℝ) ≤ Real.exp (2 * (41469 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41469 / 512000)) (1175846461 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41473 / 512000) : ℝ)) ≤ (235172967 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41473 / 512000)) (235172967 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64975318799 / 1000000) : ℝ) ≤ Real.exp (3 * (3693921 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3693921 / 1000000)) (64975318799 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41469 / 512000) : ℝ) (41473 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3693921 / 1000000) (3694097 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41469 / 512000) (41473 / 512000) (1175846461 / 1000000000) (235172967 / 200000000) (3693921 / 1000000) (3694097 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41469 / 512000) (41473 / 512000) (3693921 / 1000000) (3694097 / 1000000) (6483 / 200) (16211 / 500)
    (6156 / 125) (12337 / 250) (-276263 / 500) (398823 / 1000000) (372446 / 125) (1969979 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3693921 / 1000000) (64975318799 / 1000000) (1969979 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693921 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693921 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell332 :
    ∀ t ∈ Set.Icc ((41473 / 512000) : ℝ) (1659 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587932417 / 500000000) : ℝ) ≤ Real.exp (2 * (41473 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41473 / 512000)) (587932417 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1659 / 20480) : ℝ)) ≤ (587937011 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1659 / 20480)) (587937011 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64986625483 / 1000000) : ℝ) ≤ Real.exp (3 * (3693979 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3693979 / 1000000)) (64986625483 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41473 / 512000) : ℝ) (1659 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3693979 / 1000000) (1847063 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41473 / 512000) (1659 / 20480) (587932417 / 500000000) (587937011 / 500000000) (3693979 / 1000000) (1847063 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41473 / 512000) (1659 / 20480) (3693979 / 1000000) (1847063 / 500000) (32417 / 1000) (32423 / 1000)
    (49261 / 1000) (9869 / 200) (-110533 / 200) (99691 / 250000) (2979661 / 1000) (3939273 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3693979 / 1000000) (64986625483 / 1000000) (3939273 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693979 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693979 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell333 :
    ∀ t ∈ Set.Icc ((1659 / 20480) : ℝ) (41477 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175874021 / 1000000000) : ℝ) ≤ Real.exp (2 * (1659 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1659 / 20480)) (1175874021 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41477 / 512000) : ℝ)) ≤ (146985401 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41477 / 512000)) (146985401 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64992279563 / 1000000) : ℝ) ≤ Real.exp (3 * (461751 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (461751 / 125000)) (64992279563 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1659 / 20480) : ℝ) (41477 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (461751 / 125000) (738831 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1659 / 20480) (41477 / 512000) (1175874021 / 1000000000) (146985401 / 125000000) (461751 / 125000) (738831 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1659 / 20480) (41477 / 512000) (461751 / 125000) (738831 / 200000) (32417 / 1000) (4053 / 125)
    (9853 / 200) (49349 / 1000) (-55267 / 100) (199369 / 500000) (595951 / 200) (393893 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (461751 / 125000) (64992279563 / 1000000) (393893 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461751 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461751 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell334 :
    ∀ t ∈ Set.Icc ((41477 / 512000) : ℝ) (41481 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175883207 / 1000000000) : ℝ) ≤ Real.exp (2 * (41477 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41477 / 512000)) (1175883207 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41481 / 512000) : ℝ)) ≤ (1175901581 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41481 / 512000)) (1175901581 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((12999586827 / 200000) : ℝ) ≤ Real.exp (3 * (3694037 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3694037 / 1000000)) (12999586827 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41477 / 512000) : ℝ) (41481 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3694037 / 1000000) (3694213 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41477 / 512000) (41481 / 512000) (1175883207 / 1000000000) (1175901581 / 1000000000) (3694037 / 1000000) (3694213 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41477 / 512000) (41481 / 512000) (3694037 / 1000000) (3694213 / 1000000) (16209 / 500) (1297 / 40)
    (24631 / 500) (24681 / 500) (-276273 / 500) (199361 / 500000) (1489971 / 500) (3938587 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3694037 / 1000000) (12999586827 / 200000) (3938587 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3694037 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3694037 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell335 :
    ∀ t ∈ Set.Icc ((41481 / 512000) : ℝ) (8297 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((58795079 / 50000000) : ℝ) ≤ Real.exp (2 * (41481 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41481 / 512000)) (58795079 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8297 / 102400) : ℝ)) ≤ (235183991 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8297 / 102400)) (235183991 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65009049727 / 1000000) : ℝ) ≤ Real.exp (3 * (1847047 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1847047 / 500000)) (65009049727 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41481 / 512000) : ℝ) (8297 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1847047 / 500000) (3694271 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41481 / 512000) (8297 / 102400) (58795079 / 50000000) (235183991 / 200000000) (1847047 / 500000) (3694271 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41481 / 512000) (8297 / 102400) (1847047 / 500000) (3694271 / 1000000) (32419 / 1000) (16213 / 500)
    (12317 / 250) (49369 / 1000) (-69069 / 125) (398673 / 1000000) (2980129 / 1000) (1968957 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1847047 / 500000) (65009049727 / 1000000) (1968957 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1847047 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1847047 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell336 :
    ∀ t ∈ Set.Icc ((8297 / 102400) : ℝ) (41489 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587959977 / 500000000) : ℝ) ≤ Real.exp (2 * (8297 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8297 / 102400)) (587959977 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41489 / 512000) : ℝ)) ≤ (1175938329 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41489 / 512000)) (1175938329 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1625509057 / 25000) : ℝ) ≤ Real.exp (3 * (461769 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (461769 / 125000)) (1625509057 / 25000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8297 / 102400) : ℝ) (41489 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (461769 / 125000) (461791 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8297 / 102400) (41489 / 512000) (587959977 / 500000000) (1175938329 / 1000000000) (461769 / 125000) (461791 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8297 / 102400) (41489 / 512000) (461769 / 125000) (461791 / 125000) (32421 / 1000) (8107 / 250)
    (12319 / 250) (6172 / 125) (-552567 / 1000) (199311 / 500000) (2980313 / 1000) (3937229 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (461769 / 125000) (1625509057 / 25000) (3937229 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461769 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461769 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell337 :
    ∀ t ∈ Set.Icc ((41489 / 512000) : ℝ) (41493 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((146992291 / 125000000) : ℝ) ≤ Real.exp (2 * (41489 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41489 / 512000)) (146992291 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41493 / 512000) : ℝ)) ≤ (1175956703 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41493 / 512000)) (1175956703 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65031676803 / 1000000) : ℝ) ≤ Real.exp (3 * (369421 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (369421 / 100000)) (65031676803 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41489 / 512000) : ℝ) (41493 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (369421 / 100000) (1847193 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41489 / 512000) (41493 / 512000) (146992291 / 125000000) (1175956703 / 1000000000) (369421 / 100000) (1847193 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41489 / 512000) (41493 / 512000) (369421 / 100000) (1847193 / 500000) (16211 / 500) (32429 / 1000)
    (49283 / 1000) (49383 / 1000) (-552577 / 1000) (398571 / 1000000) (5961 / 2) (123017 / 31250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (369421 / 100000) (65031676803 / 1000000) (123017 / 31250000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (369421 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (369421 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell338 :
    ∀ t ∈ Set.Icc ((41493 / 512000) : ℝ) (8299 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587978351 / 500000000) : ℝ) ≤ Real.exp (2 * (41493 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41493 / 512000)) (587978351 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8299 / 102400) : ℝ)) ≤ (117596589 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8299 / 102400)) (117596589 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13008559633 / 200000) : ℝ) ≤ Real.exp (3 * (3694267 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3694267 / 1000000)) (13008559633 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41493 / 512000) : ℝ) (8299 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3694267 / 1000000) (738883 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41493 / 512000) (8299 / 102400) (587978351 / 500000000) (117596589 / 100000000) (3694267 / 1000000) (738883 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41493 / 512000) (8299 / 102400) (3694267 / 1000000) (738883 / 200000) (32423 / 1000) (3243 / 100)
    (6162 / 125) (2469 / 50) (-552711 / 1000) (398513 / 1000000) (1490297 / 500) (3935871 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3694267 / 1000000) (13008559633 / 200000) (3935871 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3694267 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3694267 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell339 :
    ∀ t ∈ Set.Icc ((8299 / 102400) : ℝ) (41499 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175965889 / 1000000000) : ℝ) ≤ Real.exp (2 * (8299 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8299 / 102400)) (1175965889 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41499 / 512000) : ℝ)) ≤ (235196853 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41499 / 512000)) (235196853 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16262114283 / 250000) : ℝ) ≤ Real.exp (3 * (461787 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (461787 / 125000)) (16262114283 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8299 / 102400) : ℝ) (41499 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (461787 / 125000) (3694473 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8299 / 102400) (41499 / 512000) (1175965889 / 1000000000) (235196853 / 200000000) (461787 / 125000) (3694473 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8299 / 102400) (41499 / 512000) (461787 / 125000) (3694473 / 1000000) (4053 / 125) (32431 / 1000)
    (49293 / 1000) (24697 / 500) (-138147 / 250) (398497 / 1000000) (2980781 / 1000) (491941 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (461787 / 125000) (16262114283 / 250000) (491941 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461787 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461787 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch016 :
    ∀ t ∈ Set.Icc ((41447 / 512000) : ℝ) (41499 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell320
      hpThetaDensityLowerExpCompact_cell321)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell322
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell323
      hpThetaDensityLowerExpCompact_cell324)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell325
      hpThetaDensityLowerExpCompact_cell326)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell327
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell328
      hpThetaDensityLowerExpCompact_cell329))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell330
      hpThetaDensityLowerExpCompact_cell331)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell332
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell333
      hpThetaDensityLowerExpCompact_cell334)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell335
      hpThetaDensityLowerExpCompact_cell336)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell337
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell338
      hpThetaDensityLowerExpCompact_cell339)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch016
end HodgeProofHP
