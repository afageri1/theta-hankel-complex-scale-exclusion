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
theorem hpThetaDensityLowerExpCompact_cell240 :
    ∀ t ∈ Set.Icc ((41287 / 512000) : ℝ) (41289 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235002161 / 200000000) : ℝ) ≤ Real.exp (2 * (41287 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41287 / 512000)) (235002161 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41289 / 512000) : ℝ)) ≤ (587509993 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41289 / 512000)) (587509993 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4029102991 / 62500) : ℝ) ≤ Real.exp (3 * (115353 / 31250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (115353 / 31250)) (4029102991 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41287 / 512000) : ℝ) (41289 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (115353 / 31250) (3691443 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41287 / 512000) (41289 / 512000) (235002161 / 200000000) (587509993 / 500000000) (115353 / 31250) (3691443 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41287 / 512000) (41289 / 512000) (115353 / 31250) (3691443 / 1000000) (16177 / 500) (809 / 25)
    (48937 / 1000) (49021 / 1000) (-552189 / 1000) (401111 / 1000000) (1485507 / 500) (992777 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (115353 / 31250) (4029102991 / 62500) (992777 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (115353 / 31250)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (115353 / 31250)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell241 :
    ∀ t ∈ Set.Icc ((41289 / 512000) : ℝ) (41291 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235003997 / 200000000) : ℝ) ≤ Real.exp (2 * (41289 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41289 / 512000)) (235003997 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41291 / 512000) : ℝ)) ≤ (587514583 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41291 / 512000)) (587514583 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2014726769 / 31250) : ℝ) ≤ Real.exp (3 * (147653 / 40000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (147653 / 40000)) (2014726769 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41289 / 512000) : ℝ) (41291 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (147653 / 40000) (230717 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41289 / 512000) (41291 / 512000) (235003997 / 200000000) (587514583 / 500000000) (147653 / 40000) (230717 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41289 / 512000) (41291 / 512000) (147653 / 40000) (230717 / 62500) (16177 / 500) (809 / 25)
    (48941 / 1000) (1961 / 40) (-276097 / 500) (80217 / 200000) (742777 / 250) (1985381 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (147653 / 40000) (2014726769 / 31250) (1985381 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (147653 / 40000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (147653 / 40000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell242 :
    ∀ t ∈ Set.Icc ((41291 / 512000) : ℝ) (41293 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235005833 / 200000000) : ℝ) ≤ Real.exp (2 * (41291 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41291 / 512000)) (235005833 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41293 / 512000) : ℝ)) ≤ (587519173 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41293 / 512000)) (587519173 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64476865849 / 1000000) : ℝ) ≤ Real.exp (3 * (1845677 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1845677 / 500000)) (64476865849 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41291 / 512000) : ℝ) (41293 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1845677 / 500000) (3691501 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41291 / 512000) (41293 / 512000) (235005833 / 200000000) (587519173 / 500000000) (1845677 / 500000) (3691501 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41291 / 512000) (41293 / 512000) (1845677 / 500000) (3691501 / 1000000) (6471 / 200) (32361 / 1000)
    (6118 / 125) (12257 / 250) (-552199 / 1000) (20053 / 50000) (2971201 / 1000) (3970417 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1845677 / 500000) (64476865849 / 1000000) (3970417 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1845677 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1845677 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell243 :
    ∀ t ∈ Set.Icc ((41293 / 512000) : ℝ) (8259 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235007669 / 200000000) : ℝ) ≤ Real.exp (2 * (41293 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41293 / 512000)) (235007669 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8259 / 102400) : ℝ)) ≤ (587523763 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8259 / 102400)) (587523763 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64482282131 / 1000000) : ℝ) ≤ Real.exp (3 * (1845691 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1845691 / 500000)) (64482282131 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41293 / 512000) : ℝ) (8259 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1845691 / 500000) (369153 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41293 / 512000) (8259 / 102400) (235007669 / 200000000) (587523763 / 500000000) (1845691 / 500000) (369153 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41293 / 512000) (8259 / 102400) (1845691 / 500000) (369153 / 100000) (8089 / 250) (16181 / 500)
    (48947 / 1000) (6129 / 125) (-552199 / 1000) (100259 / 250000) (1485647 / 500) (3970083 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1845691 / 500000) (64482282131 / 1000000) (3970083 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1845691 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1845691 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell244 :
    ∀ t ∈ Set.Icc ((8259 / 102400) : ℝ) (41297 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((47001901 / 40000000) : ℝ) ≤ Real.exp (2 * (8259 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8259 / 102400)) (47001901 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41297 / 512000) : ℝ)) ≤ (587528353 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41297 / 512000)) (587528353 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64487892331 / 1000000) : ℝ) ≤ Real.exp (3 * (3691411 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3691411 / 1000000)) (64487892331 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8259 / 102400) : ℝ) (41297 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3691411 / 1000000) (3691559 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8259 / 102400) (41297 / 512000) (47001901 / 40000000) (587528353 / 500000000) (3691411 / 1000000) (3691559 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8259 / 102400) (41297 / 512000) (3691411 / 1000000) (3691559 / 1000000) (8089 / 250) (16181 / 500)
    (48951 / 1000) (9807 / 200) (-110441 / 200) (40101 / 100000) (742847 / 250) (1984869 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3691411 / 1000000) (64487892331 / 1000000) (1984869 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3691411 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3691411 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell245 :
    ∀ t ∈ Set.Icc ((41297 / 512000) : ℝ) (41299 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235011341 / 200000000) : ℝ) ≤ Real.exp (2 * (41297 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41297 / 512000)) (235011341 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41299 / 512000) : ℝ)) ≤ (587532943 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41299 / 512000)) (587532943 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64493503019 / 1000000) : ℝ) ≤ Real.exp (3 * (46143 / 12500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (46143 / 12500)) (64493503019 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41297 / 512000) : ℝ) (41299 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (46143 / 12500) (3691587 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41297 / 512000) (41299 / 512000) (235011341 / 200000000) (587532943 / 500000000) (46143 / 12500) (3691587 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41297 / 512000) (41299 / 512000) (46143 / 12500) (3691587 / 1000000) (32357 / 1000) (32363 / 1000)
    (9791 / 200) (49039 / 1000) (-276107 / 500) (80197 / 200000) (1485739 / 500) (3969393 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (46143 / 12500) (64493503019 / 1000000) (3969393 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (46143 / 12500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (46143 / 12500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell246 :
    ∀ t ∈ Set.Icc ((41299 / 512000) : ℝ) (41301 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235013177 / 200000000) : ℝ) ≤ Real.exp (2 * (41299 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41299 / 512000)) (235013177 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41301 / 512000) : ℝ)) ≤ (587537533 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41301 / 512000)) (587537533 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16124778549 / 250000) : ℝ) ≤ Real.exp (3 * (3691469 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3691469 / 1000000)) (16124778549 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41299 / 512000) : ℝ) (41301 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3691469 / 1000000) (115363 / 31250) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41299 / 512000) (41301 / 512000) (235013177 / 200000000) (587537533 / 500000000) (3691469 / 1000000) (115363 / 31250) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41299 / 512000) (41301 / 512000) (3691469 / 1000000) (115363 / 31250) (16179 / 500) (8091 / 250)
    (24479 / 500) (24521 / 500) (-552219 / 1000) (400959 / 1000000) (2971571 / 1000) (3969047 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3691469 / 1000000) (16124778549 / 250000) (3969047 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3691469 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3691469 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell247 :
    ∀ t ∈ Set.Icc ((41301 / 512000) : ℝ) (41303 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235015013 / 200000000) : ℝ) ≤ Real.exp (2 * (41301 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41301 / 512000)) (235015013 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41303 / 512000) : ℝ)) ≤ (1175084247 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41303 / 512000)) (1175084247 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3225236293 / 50000) : ℝ) ≤ Real.exp (3 * (1845749 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1845749 / 500000)) (3225236293 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41301 / 512000) : ℝ) (41303 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1845749 / 500000) (738329 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41301 / 512000) (41303 / 512000) (235015013 / 200000000) (1175084247 / 1000000000) (1845749 / 500000) (738329 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41301 / 512000) (41303 / 512000) (1845749 / 500000) (738329 / 200000) (16179 / 500) (8091 / 250)
    (24481 / 500) (24523 / 500) (-22089 / 40) (200467 / 500000) (594333 / 200) (1984351 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1845749 / 500000) (3225236293 / 50000) (1984351 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1845749 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1845749 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell248 :
    ∀ t ∈ Set.Icc ((41303 / 512000) : ℝ) (8261 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587542123 / 500000000) : ℝ) ≤ Real.exp (2 * (41303 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41303 / 512000)) (587542123 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8261 / 102400) : ℝ)) ≤ (1175093427 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8261 / 102400)) (1175093427 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64510338013 / 1000000) : ℝ) ≤ Real.exp (3 * (3691527 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3691527 / 1000000)) (64510338013 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41303 / 512000) : ℝ) (8261 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3691527 / 1000000) (1845837 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41303 / 512000) (8261 / 102400) (587542123 / 500000000) (1175093427 / 1000000000) (3691527 / 1000000) (1845837 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41303 / 512000) (8261 / 102400) (3691527 / 1000000) (1845837 / 500000) (32359 / 1000) (6473 / 200)
    (9793 / 200) (49049 / 1000) (-55223 / 100) (100227 / 250000) (1485879 / 500) (3968357 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3691527 / 1000000) (64510338013 / 1000000) (3968357 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3691527 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3691527 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell249 :
    ∀ t ∈ Set.Icc ((8261 / 102400) : ℝ) (41307 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587546713 / 500000000) : ℝ) ≤ Real.exp (2 * (8261 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8261 / 102400)) (587546713 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41307 / 512000) : ℝ)) ≤ (1175102607 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41307 / 512000)) (1175102607 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64515757107 / 1000000) : ℝ) ≤ Real.exp (3 * (738311 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (738311 / 200000)) (64515757107 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8261 / 102400) : ℝ) (41307 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (738311 / 200000) (3691703 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8261 / 102400) (41307 / 512000) (587546713 / 500000000) (1175102607 / 1000000000) (738311 / 200000) (3691703 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8261 / 102400) (41307 / 512000) (738311 / 200000) (3691703 / 1000000) (809 / 25) (16183 / 500)
    (6121 / 125) (49053 / 1000) (-55223 / 100) (100221 / 250000) (2971851 / 1000) (3968023 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (738311 / 200000) (64515757107 / 1000000) (3968023 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (738311 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (738311 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell250 :
    ∀ t ∈ Set.Icc ((41307 / 512000) : ℝ) (41309 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587551303 / 500000000) : ℝ) ≤ Real.exp (2 * (41307 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41307 / 512000)) (587551303 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41309 / 512000) : ℝ)) ≤ (293777947 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41309 / 512000)) (293777947 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64521370219 / 1000000) : ℝ) ≤ Real.exp (3 * (57681 / 15625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (57681 / 15625)) (64521370219 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41307 / 512000) : ℝ) (41309 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (57681 / 15625) (922933 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41307 / 512000) (41309 / 512000) (587551303 / 500000000) (293777947 / 250000000) (57681 / 15625) (922933 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41307 / 512000) (41309 / 512000) (57681 / 15625) (922933 / 250000) (809 / 25) (32367 / 1000)
    (12243 / 250) (6132 / 125) (-110447 / 200) (400859 / 1000000) (594389 / 200) (1983839 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (57681 / 15625) (64521370219 / 1000000) (1983839 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (57681 / 15625)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (57681 / 15625)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell251 :
    ∀ t ∈ Set.Icc ((41309 / 512000) : ℝ) (41311 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175111787 / 1000000000) : ℝ) ≤ Real.exp (2 * (41309 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41309 / 512000)) (1175111787 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41311 / 512000) : ℝ)) ≤ (146890121 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41311 / 512000)) (146890121 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3226349191 / 50000) : ℝ) ≤ Real.exp (3 * (3691613 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3691613 / 1000000)) (3226349191 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41309 / 512000) : ℝ) (41311 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3691613 / 1000000) (3691761 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41309 / 512000) (41311 / 512000) (1175111787 / 1000000000) (146890121 / 125000000) (3691613 / 1000000) (3691761 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41309 / 512000) (41311 / 512000) (3691613 / 1000000) (3691761 / 1000000) (32361 / 1000) (32367 / 1000)
    (1959 / 40) (2453 / 50) (-552241 / 1000) (400833 / 1000000) (1486019 / 500) (3967333 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3691613 / 1000000) (3226349191 / 50000) (3967333 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3691613 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3691613 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell252 :
    ∀ t ∈ Set.Icc ((41311 / 512000) : ℝ) (41313 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175120967 / 1000000000) : ℝ) ≤ Real.exp (2 * (41311 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41311 / 512000)) (1175120967 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41313 / 512000) : ℝ)) ≤ (1175130149 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41313 / 512000)) (1175130149 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64532597909 / 1000000) : ℝ) ≤ Real.exp (3 * (1845821 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1845821 / 500000)) (64532597909 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41311 / 512000) : ℝ) (41313 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1845821 / 500000) (3691789 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41311 / 512000) (41313 / 512000) (1175120967 / 1000000000) (1175130149 / 1000000000) (1845821 / 500000) (3691789 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41311 / 512000) (41313 / 512000) (1845821 / 500000) (3691789 / 1000000) (16181 / 500) (4046 / 125)
    (48979 / 1000) (49063 / 1000) (-2209 / 4) (400807 / 1000000) (371516 / 125) (991747 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1845821 / 500000) (64532597909 / 1000000) (991747 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1845821 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1845821 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell253 :
    ∀ t ∈ Set.Icc ((41313 / 512000) : ℝ) (8263 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293782537 / 250000000) : ℝ) ≤ Real.exp (2 * (41313 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41313 / 512000)) (293782537 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8263 / 102400) : ℝ)) ≤ (117513933 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8263 / 102400)) (117513933 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64538212487 / 1000000) : ℝ) ≤ Real.exp (3 * (3691671 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3691671 / 1000000)) (64538212487 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41313 / 512000) : ℝ) (8263 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3691671 / 1000000) (1845909 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41313 / 512000) (8263 / 102400) (293782537 / 250000000) (117513933 / 100000000) (3691671 / 1000000) (1845909 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41313 / 512000) (8263 / 102400) (3691671 / 1000000) (1845909 / 500000) (16181 / 500) (32369 / 1000)
    (48983 / 1000) (24533 / 500) (-110451 / 200) (200391 / 500000) (1486111 / 500) (3966643 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3691671 / 1000000) (64538212487 / 1000000) (3966643 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3691671 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3691671 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell254 :
    ∀ t ∈ Set.Icc ((8263 / 102400) : ℝ) (41317 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175139329 / 1000000000) : ℝ) ≤ Real.exp (2 * (8263 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8263 / 102400)) (1175139329 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41317 / 512000) : ℝ)) ≤ (1175148511 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41317 / 512000)) (1175148511 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64543827553 / 1000000) : ℝ) ≤ Real.exp (3 * (36917 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (36917 / 10000)) (64543827553 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8263 / 102400) : ℝ) (41317 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (36917 / 10000) (3691847 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8263 / 102400) (41317 / 512000) (1175139329 / 1000000000) (1175148511 / 1000000000) (36917 / 10000) (3691847 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8263 / 102400) (41317 / 512000) (36917 / 10000) (3691847 / 1000000) (32363 / 1000) (32369 / 1000)
    (24493 / 500) (4907 / 100) (-552261 / 1000) (400757 / 1000000) (594463 / 200) (1983149 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (36917 / 10000) (64543827553 / 1000000) (1983149 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (36917 / 10000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (36917 / 10000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell255 :
    ∀ t ∈ Set.Icc ((41317 / 512000) : ℝ) (41319 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((117514851 / 100000000) : ℝ) ≤ Real.exp (2 * (41317 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41317 / 512000)) (117514851 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41319 / 512000) : ℝ)) ≤ (293789423 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41319 / 512000)) (293789423 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16137360777 / 250000) : ℝ) ≤ Real.exp (3 * (3691729 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3691729 / 1000000)) (16137360777 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41317 / 512000) : ℝ) (41319 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3691729 / 1000000) (922969 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41317 / 512000) (41319 / 512000) (117514851 / 100000000) (293789423 / 250000000) (3691729 / 1000000) (922969 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41317 / 512000) (41319 / 512000) (3691729 / 1000000) (922969 / 250000) (8091 / 250) (3237 / 100)
    (4899 / 100) (49073 / 1000) (-276133 / 500) (400731 / 1000000) (371551 / 125) (3965953 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3691729 / 1000000) (16137360777 / 250000) (3965953 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3691729 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3691729 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell256 :
    ∀ t ∈ Set.Icc ((41319 / 512000) : ℝ) (41321 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175157691 / 1000000000) : ℝ) ≤ Real.exp (2 * (41319 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41319 / 512000)) (1175157691 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41321 / 512000) : ℝ)) ≤ (1175166873 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41321 / 512000)) (1175166873 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64554865487 / 1000000) : ℝ) ≤ Real.exp (3 * (3691757 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3691757 / 1000000)) (64554865487 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41319 / 512000) : ℝ) (41321 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3691757 / 1000000) (738381 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41319 / 512000) (41321 / 512000) (1175157691 / 1000000000) (1175166873 / 1000000000) (3691757 / 1000000) (738381 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41319 / 512000) (41321 / 512000) (3691757 / 1000000) (738381 / 200000) (8091 / 250) (32371 / 1000)
    (48993 / 1000) (49077 / 1000) (-276133 / 500) (400707 / 1000000) (1486251 / 500) (3965619 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3691757 / 1000000) (64554865487 / 1000000) (3965619 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3691757 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3691757 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell257 :
    ∀ t ∈ Set.Icc ((41321 / 512000) : ℝ) (41323 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((146895859 / 125000000) : ℝ) ≤ Real.exp (2 * (41321 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41321 / 512000)) (146895859 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41323 / 512000) : ℝ)) ≤ (587588027 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41323 / 512000)) (587588027 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32280241001 / 500000) : ℝ) ≤ Real.exp (3 * (1845893 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1845893 / 500000)) (32280241001 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41321 / 512000) : ℝ) (41323 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1845893 / 500000) (1845967 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41321 / 512000) (41323 / 512000) (146895859 / 125000000) (587588027 / 500000000) (1845893 / 500000) (1845967 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41321 / 512000) (41323 / 512000) (1845893 / 500000) (1845967 / 500000) (6473 / 200) (32371 / 1000)
    (12249 / 250) (49081 / 1000) (-552271 / 1000) (400681 / 1000000) (594519 / 200) (1982637 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1845893 / 500000) (32280241001 / 500000) (1982637 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1845893 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1845893 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell258 :
    ∀ t ∈ Set.Icc ((41323 / 512000) : ℝ) (1653 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175176053 / 1000000000) : ℝ) ≤ Real.exp (2 * (41323 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41323 / 512000)) (1175176053 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1653 / 20480) : ℝ)) ≤ (235037047 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1653 / 20480)) (235037047 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((12913219801 / 200000) : ℝ) ≤ Real.exp (3 * (738363 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (738363 / 200000)) (12913219801 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41323 / 512000) : ℝ) (1653 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (738363 / 200000) (1845981 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41323 / 512000) (1653 / 20480) (1175176053 / 1000000000) (235037047 / 200000000) (738363 / 200000) (1845981 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41323 / 512000) (1653 / 20480) (738363 / 200000) (1845981 / 500000) (16183 / 500) (8093 / 250)
    (49) (12271 / 250) (-552281 / 1000) (25041 / 62500) (594537 / 200) (396493 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (738363 / 200000) (12913219801 / 200000) (396493 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (738363 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (738363 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell259 :
    ∀ t ∈ Set.Icc ((1653 / 20480) : ℝ) (41327 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587592617 / 500000000) : ℝ) ≤ Real.exp (2 * (1653 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1653 / 20480)) (587592617 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41327 / 512000) : ℝ)) ≤ (73449651 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41327 / 512000)) (73449651 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32285858249 / 500000) : ℝ) ≤ Real.exp (3 * (922961 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (922961 / 250000)) (32285858249 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1653 / 20480) : ℝ) (41327 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (922961 / 250000) (3691991 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1653 / 20480) (41327 / 512000) (587592617 / 500000000) (73449651 / 62500000) (922961 / 250000) (3691991 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1653 / 20480) (41327 / 512000) (922961 / 250000) (3691991 / 1000000) (16183 / 500) (32373 / 1000)
    (49003 / 1000) (49087 / 1000) (-276143 / 500) (40063 / 100000) (2972779 / 1000) (792917 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (922961 / 250000) (32285858249 / 500000) (792917 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922961 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922961 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch012 :
    ∀ t ∈ Set.Icc ((41287 / 512000) : ℝ) (41327 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell240
      hpThetaDensityLowerExpCompact_cell241)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell242
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell243
      hpThetaDensityLowerExpCompact_cell244)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell245
      hpThetaDensityLowerExpCompact_cell246)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell247
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell248
      hpThetaDensityLowerExpCompact_cell249))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell250
      hpThetaDensityLowerExpCompact_cell251)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell252
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell253
      hpThetaDensityLowerExpCompact_cell254)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell255
      hpThetaDensityLowerExpCompact_cell256)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell257
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell258
      hpThetaDensityLowerExpCompact_cell259)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch012
end HodgeProofHP
