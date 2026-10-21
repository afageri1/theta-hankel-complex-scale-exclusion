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
theorem hpThetaDensityLowerExpCompact_cell300 :
    ∀ t ∈ Set.Icc ((41407 / 512000) : ℝ) (41409 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((29389043 / 25000000) : ℝ) ≤ Real.exp (2 * (41407 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41407 / 512000)) (29389043 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41409 / 512000) : ℝ)) ≤ (587785453 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41409 / 512000)) (587785453 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64801288551 / 1000000) : ℝ) ≤ Real.exp (3 * (3693027 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3693027 / 1000000)) (64801288551 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41407 / 512000) : ℝ) (41409 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3693027 / 1000000) (1846587 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41407 / 512000) (41409 / 512000) (29389043 / 25000000) (587785453 / 500000000) (3693027 / 1000000) (1846587 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41407 / 512000) (41409 / 512000) (3693027 / 1000000) (1846587 / 500000) (16197 / 500) (162 / 5)
    (24573 / 500) (4923 / 100) (-69062 / 125) (79919 / 200000) (2976591 / 1000) (3950539 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3693027 / 1000000) (64801288551 / 1000000) (3950539 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693027 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693027 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell301 :
    ∀ t ∈ Set.Icc ((41409 / 512000) : ℝ) (41411 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235114181 / 200000000) : ℝ) ≤ Real.exp (2 * (41409 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41409 / 512000)) (235114181 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41411 / 512000) : ℝ)) ≤ (117558009 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41411 / 512000)) (117558009 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32403366043 / 500000) : ℝ) ≤ Real.exp (3 * (738611 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (738611 / 200000)) (32403366043 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41409 / 512000) : ℝ) (41411 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (738611 / 200000) (3693203 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41409 / 512000) (41411 / 512000) (235114181 / 200000000) (117558009 / 100000000) (738611 / 200000) (3693203 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41409 / 512000) (41411 / 512000) (738611 / 200000) (3693203 / 1000000) (6479 / 200) (32401 / 1000)
    (49149 / 1000) (24617 / 500) (-552497 / 1000) (399571 / 1000000) (744171 / 250) (3950207 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (738611 / 200000) (32403366043 / 500000) (3950207 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (738611 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (738611 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell302 :
    ∀ t ∈ Set.Icc ((41411 / 512000) : ℝ) (41413 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175580089 / 1000000000) : ℝ) ≤ Real.exp (2 * (41411 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41411 / 512000)) (1175580089 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41413 / 512000) : ℝ)) ≤ (587794637 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41413 / 512000)) (587794637 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32406185257 / 500000) : ℝ) ≤ Real.exp (3 * (923271 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (923271 / 250000)) (32406185257 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41411 / 512000) : ℝ) (41413 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (923271 / 250000) (230827 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41411 / 512000) (41413 / 512000) (1175580089 / 1000000000) (587794637 / 500000000) (923271 / 250000) (230827 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41411 / 512000) (41413 / 512000) (923271 / 250000) (230827 / 62500) (8099 / 250) (16201 / 500)
    (49153 / 1000) (49237 / 1000) (-276251 / 500) (79909 / 200000) (1488389 / 500) (493733 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (923271 / 250000) (32406185257 / 500000) (493733 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (923271 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (923271 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell303 :
    ∀ t ∈ Set.Icc ((41413 / 512000) : ℝ) (8283 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175589273 / 1000000000) : ℝ) ≤ Real.exp (2 * (41413 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41413 / 512000)) (1175589273 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8283 / 102400) : ℝ)) ≤ (587799229 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8283 / 102400)) (587799229 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64818009433 / 1000000) : ℝ) ≤ Real.exp (3 * (3693113 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3693113 / 1000000)) (64818009433 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41413 / 512000) : ℝ) (8283 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3693113 / 1000000) (3693261 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41413 / 512000) (8283 / 102400) (1175589273 / 1000000000) (587799229 / 500000000) (3693113 / 1000000) (3693261 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41413 / 512000) (8283 / 102400) (3693113 / 1000000) (3693261 / 1000000) (8099 / 250) (32403 / 1000)
    (12289 / 250) (49241 / 1000) (-552507 / 1000) (2497 / 6250) (2976871 / 1000) (49369 / 12500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3693113 / 1000000) (64818009433 / 1000000) (49369 / 12500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693113 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693113 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell304 :
    ∀ t ∈ Set.Icc ((8283 / 102400) : ℝ) (41417 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175598457 / 1000000000) : ℝ) ≤ Real.exp (2 * (8283 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8283 / 102400)) (1175598457 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41417 / 512000) : ℝ)) ≤ (1175607643 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41417 / 512000)) (1175607643 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64823648843 / 1000000) : ℝ) ≤ Real.exp (3 * (1846571 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1846571 / 500000)) (64823648843 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8283 / 102400) : ℝ) (41417 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1846571 / 500000) (3693289 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8283 / 102400) (41417 / 512000) (1175598457 / 1000000000) (1175607643 / 1000000000) (1846571 / 500000) (3693289 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8283 / 102400) (41417 / 512000) (1846571 / 500000) (3693289 / 1000000) (32397 / 1000) (32403 / 1000)
    (1229 / 25) (12311 / 250) (-552517 / 1000) (199747 / 500000) (1488481 / 500) (3949177 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1846571 / 500000) (64823648843 / 1000000) (3949177 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1846571 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1846571 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell305 :
    ∀ t ∈ Set.Icc ((41417 / 512000) : ℝ) (41419 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587803821 / 500000000) : ℝ) ≤ Real.exp (2 * (41417 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41417 / 512000)) (587803821 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41419 / 512000) : ℝ)) ≤ (1175616827 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41419 / 512000)) (1175616827 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64829288743 / 1000000) : ℝ) ≤ Real.exp (3 * (3693171 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3693171 / 1000000)) (64829288743 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41417 / 512000) : ℝ) (41419 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3693171 / 1000000) (1846659 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41417 / 512000) (41419 / 512000) (587803821 / 500000000) (1175616827 / 1000000000) (3693171 / 1000000) (1846659 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41417 / 512000) (41419 / 512000) (3693171 / 1000000) (1846659 / 500000) (16199 / 500) (8101 / 250)
    (12291 / 250) (49247 / 1000) (-276261 / 500) (399469 / 1000000) (595411 / 200) (3948833 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3693171 / 1000000) (64829288743 / 1000000) (3948833 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693171 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693171 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell306 :
    ∀ t ∈ Set.Icc ((41419 / 512000) : ℝ) (41421 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587808413 / 500000000) : ℝ) ≤ Real.exp (2 * (41419 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41419 / 512000)) (587808413 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41421 / 512000) : ℝ)) ≤ (293906503 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41421 / 512000)) (293906503 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32417464567 / 500000) : ℝ) ≤ Real.exp (3 * (9233 / 2500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (9233 / 2500)) (32417464567 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41419 / 512000) : ℝ) (41421 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (9233 / 2500) (3693347 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41419 / 512000) (41421 / 512000) (587808413 / 500000000) (293906503 / 250000000) (9233 / 2500) (3693347 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41419 / 512000) (41421 / 512000) (9233 / 2500) (3693347 / 1000000) (16199 / 500) (6481 / 200)
    (49167 / 1000) (49251 / 1000) (-552527 / 1000) (99861 / 250000) (2977149 / 1000) (3948489 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (9233 / 2500) (32417464567 / 500000) (3948489 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (9233 / 2500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (9233 / 2500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell307 :
    ∀ t ∈ Set.Icc ((41421 / 512000) : ℝ) (41423 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175626011 / 1000000000) : ℝ) ≤ Real.exp (2 * (41421 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41421 / 512000)) (1175626011 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41423 / 512000) : ℝ)) ≤ (293908799 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41423 / 512000)) (293908799 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2026267813 / 31250) : ℝ) ≤ Real.exp (3 * (3693229 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3693229 / 1000000)) (2026267813 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41421 / 512000) : ℝ) (41423 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3693229 / 1000000) (57709 / 15625) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41421 / 512000) (41423 / 512000) (1175626011 / 1000000000) (293908799 / 250000000) (3693229 / 1000000) (57709 / 15625) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41421 / 512000) (41423 / 512000) (3693229 / 1000000) (57709 / 15625) (32399 / 1000) (6481 / 200)
    (49171 / 1000) (24627 / 500) (-138133 / 250) (199709 / 500000) (1488621 / 500) (1974073 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3693229 / 1000000) (2026267813 / 31250) (1974073 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693229 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693229 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell308 :
    ∀ t ∈ Set.Icc ((41423 / 512000) : ℝ) (1657 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235127039 / 200000000) : ℝ) ≤ Real.exp (2 * (41423 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41423 / 512000)) (235127039 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1657 / 20480) : ℝ)) ≤ (1175644381 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1657 / 20480)) (1175644381 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1296920337 / 20000) : ℝ) ≤ Real.exp (3 * (3693257 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3693257 / 1000000)) (1296920337 / 20000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41423 / 512000) : ℝ) (1657 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3693257 / 1000000) (738681 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41423 / 512000) (1657 / 20480) (235127039 / 200000000) (1175644381 / 1000000000) (3693257 / 1000000) (738681 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41423 / 512000) (1657 / 20480) (3693257 / 1000000) (738681 / 200000) (162 / 5) (16203 / 500)
    (24587 / 500) (24629 / 500) (-552533 / 1000) (199697 / 500000) (372167 / 125) (1973907 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3693257 / 1000000) (1296920337 / 20000) (1973907 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693257 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693257 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell309 :
    ∀ t ∈ Set.Icc ((1657 / 20480) : ℝ) (41427 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((58782219 / 50000000) : ℝ) ≤ Real.exp (2 * (1657 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1657 / 20480)) (58782219 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41427 / 512000) : ℝ)) ≤ (587826783 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41427 / 512000)) (587826783 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8106457337 / 125000) : ℝ) ≤ Real.exp (3 * (1846643 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1846643 / 500000)) (8106457337 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1657 / 20480) : ℝ) (41427 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1846643 / 500000) (1846717 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1657 / 20480) (41427 / 512000) (58782219 / 50000000) (587826783 / 500000000) (1846643 / 500000) (1846717 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1657 / 20480) (41427 / 512000) (1846643 / 500000) (1846717 / 500000) (162 / 5) (32407 / 1000)
    (49177 / 1000) (24631 / 500) (-276269 / 500) (399369 / 1000000) (2977429 / 1000) (3947471 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1846643 / 500000) (8106457337 / 125000) (3947471 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1846643 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1846643 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell310 :
    ∀ t ∈ Set.Icc ((41427 / 512000) : ℝ) (41429 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235130713 / 200000000) : ℝ) ≤ Real.exp (2 * (41427 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41427 / 512000)) (235130713 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41429 / 512000) : ℝ)) ≤ (1175662751 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41429 / 512000)) (1175662751 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64857301033 / 1000000) : ℝ) ≤ Real.exp (3 * (738663 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (738663 / 200000)) (64857301033 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41427 / 512000) : ℝ) (41429 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (738663 / 200000) (3693463 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41427 / 512000) (41429 / 512000) (235130713 / 200000000) (1175662751 / 1000000000) (738663 / 200000) (3693463 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41427 / 512000) (41429 / 512000) (738663 / 200000) (3693463 / 1000000) (32401 / 1000) (32407 / 1000)
    (49181 / 1000) (9853 / 200) (-552543 / 1000) (399343 / 1000000) (2977523 / 1000) (3947127 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (738663 / 200000) (64857301033 / 1000000) (3947127 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (738663 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (738663 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell311 :
    ∀ t ∈ Set.Icc ((41429 / 512000) : ℝ) (41431 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((4702651 / 4000000) : ℝ) ≤ Real.exp (2 * (41429 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41429 / 512000)) (4702651 / 4000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41431 / 512000) : ℝ)) ≤ (9184937 / 7812500) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41431 / 512000)) (9184937 / 7812500) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32431471931 / 500000) : ℝ) ≤ Real.exp (3 * (115417 / 31250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (115417 / 31250)) (32431471931 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41429 / 512000) : ℝ) (41431 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (115417 / 31250) (3693491 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41429 / 512000) (41431 / 512000) (4702651 / 4000000) (9184937 / 7812500) (115417 / 31250) (3693491 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41429 / 512000) (41431 / 512000) (115417 / 31250) (3693491 / 1000000) (16201 / 500) (4051 / 125)
    (6148 / 125) (12317 / 250) (-552553 / 1000) (199659 / 500000) (2977613 / 1000) (123337 / 31250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (115417 / 31250) (32431471931 / 500000) (123337 / 31250000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (115417 / 31250)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (115417 / 31250)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell312 :
    ∀ t ∈ Set.Icc ((41431 / 512000) : ℝ) (41433 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235134387 / 200000000) : ℝ) ≤ Real.exp (2 * (41431 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41431 / 512000)) (235134387 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41433 / 512000) : ℝ)) ≤ (1175681121 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41433 / 512000)) (1175681121 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64868587181 / 1000000) : ℝ) ≤ Real.exp (3 * (3693373 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3693373 / 1000000)) (64868587181 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41431 / 512000) : ℝ) (41433 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3693373 / 1000000) (46169 / 12500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41431 / 512000) (41433 / 512000) (235134387 / 200000000) (1175681121 / 1000000000) (3693373 / 1000000) (46169 / 12500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41431 / 512000) (41433 / 512000) (3693373 / 1000000) (46169 / 12500) (16201 / 500) (32409 / 1000)
    (12297 / 250) (6159 / 125) (-276279 / 500) (399293 / 1000000) (1488853 / 500) (3946441 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3693373 / 1000000) (64868587181 / 1000000) (3946441 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693373 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693373 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell313 :
    ∀ t ∈ Set.Icc ((41433 / 512000) : ℝ) (8287 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((7348007 / 6250000) : ℝ) ≤ Real.exp (2 * (41433 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41433 / 512000)) (7348007 / 6250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8287 / 102400) : ℝ)) ≤ (587845153 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8287 / 102400)) (587845153 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64874230991 / 1000000) : ℝ) ≤ Real.exp (3 * (1846701 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1846701 / 500000)) (64874230991 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41433 / 512000) : ℝ) (8287 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1846701 / 500000) (3693549 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41433 / 512000) (8287 / 102400) (7348007 / 6250000) (587845153 / 500000000) (1846701 / 500000) (3693549 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41433 / 512000) (8287 / 102400) (1846701 / 500000) (3693549 / 1000000) (32403 / 1000) (32409 / 1000)
    (49191 / 1000) (1971 / 40) (-552563 / 1000) (399267 / 1000000) (14889 / 5) (3946097 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1846701 / 500000) (64874230991 / 1000000) (3946097 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1846701 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1846701 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell314 :
    ∀ t ∈ Set.Icc ((8287 / 102400) : ℝ) (41437 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235138061 / 200000000) : ℝ) ≤ Real.exp (2 * (8287 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8287 / 102400)) (235138061 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41437 / 512000) : ℝ)) ≤ (1175699491 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41437 / 512000)) (1175699491 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16219968823 / 250000) : ℝ) ≤ Real.exp (3 * (3693431 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3693431 / 1000000)) (16219968823 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8287 / 102400) : ℝ) (41437 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3693431 / 1000000) (1846789 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8287 / 102400) (41437 / 512000) (235138061 / 200000000) (1175699491 / 1000000000) (3693431 / 1000000) (1846789 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8287 / 102400) (41437 / 512000) (3693431 / 1000000) (1846789 / 500000) (8101 / 250) (3241 / 100)
    (9839 / 200) (49279 / 1000) (-69071 / 125) (199621 / 500000) (2977893 / 1000) (1972877 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3693431 / 1000000) (16219968823 / 250000) (1972877 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693431 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693431 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell315 :
    ∀ t ∈ Set.Icc ((41437 / 512000) : ℝ) (41439 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((117569949 / 100000000) : ℝ) ≤ Real.exp (2 * (41437 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41437 / 512000)) (117569949 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41439 / 512000) : ℝ)) ≤ (293927169 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41439 / 512000)) (293927169 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16221331357 / 250000) : ℝ) ≤ Real.exp (3 * (3693459 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3693459 / 1000000)) (16221331357 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41437 / 512000) : ℝ) (41439 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3693459 / 1000000) (3693607 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41437 / 512000) (41439 / 512000) (117569949 / 100000000) (293927169 / 250000000) (3693459 / 1000000) (3693607 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41437 / 512000) (41439 / 512000) (3693459 / 1000000) (3693607 / 1000000) (8101 / 250) (32411 / 1000)
    (24599 / 500) (49283 / 1000) (-69071 / 125) (199609 / 500000) (2977987 / 1000) (3945423 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3693459 / 1000000) (16221331357 / 250000) (3945423 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693459 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693459 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell316 :
    ∀ t ∈ Set.Icc ((41439 / 512000) : ℝ) (41441 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((47028347 / 40000000) : ℝ) ≤ Real.exp (2 * (41439 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41439 / 512000)) (47028347 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41441 / 512000) : ℝ)) ≤ (1175717861 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41441 / 512000)) (1175717861 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32445485347 / 500000) : ℝ) ≤ Real.exp (3 * (230843 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (230843 / 62500)) (32445485347 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41439 / 512000) : ℝ) (41441 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (230843 / 62500) (923409 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41439 / 512000) (41441 / 512000) (47028347 / 40000000) (1175717861 / 1000000000) (230843 / 62500) (923409 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41439 / 512000) (41441 / 512000) (230843 / 62500) (923409 / 250000) (6481 / 200) (32411 / 1000)
    (24601 / 500) (24643 / 500) (-276287 / 500) (49899 / 125000) (2978081 / 1000) (3945079 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (230843 / 62500) (32445485347 / 500000) (3945079 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (230843 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (230843 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell317 :
    ∀ t ∈ Set.Icc ((41441 / 512000) : ℝ) (41443 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((58785893 / 50000000) : ℝ) ≤ Real.exp (2 * (41441 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41441 / 512000)) (58785893 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41443 / 512000) : ℝ)) ≤ (587863523 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41443 / 512000)) (587863523 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16224154113 / 250000) : ℝ) ≤ Real.exp (3 * (3693517 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3693517 / 1000000)) (16224154113 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41441 / 512000) : ℝ) (41443 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3693517 / 1000000) (738733 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41441 / 512000) (41443 / 512000) (58785893 / 50000000) (587863523 / 500000000) (3693517 / 1000000) (738733 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41441 / 512000) (41443 / 512000) (3693517 / 1000000) (738733 / 200000) (16203 / 500) (8103 / 250)
    (9841 / 200) (4929 / 100) (-552579 / 1000) (399167 / 1000000) (1489087 / 500) (123273 / 31250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3693517 / 1000000) (16224154113 / 250000) (123273 / 31250000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693517 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693517 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell318 :
    ∀ t ∈ Set.Icc ((41443 / 512000) : ℝ) (8289 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235145409 / 200000000) : ℝ) ≤ Real.exp (2 * (41443 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41443 / 512000)) (235145409 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8289 / 102400) : ℝ)) ≤ (146967029 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8289 / 102400)) (146967029 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((649022627 / 10000) : ℝ) ≤ Real.exp (3 * (1846773 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1846773 / 500000)) (649022627 / 10000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41443 / 512000) : ℝ) (8289 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1846773 / 500000) (3693693 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41443 / 512000) (8289 / 102400) (235145409 / 200000000) (146967029 / 125000000) (1846773 / 500000) (3693693 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41443 / 512000) (8289 / 102400) (1846773 / 500000) (3693693 / 1000000) (16203 / 500) (32413 / 1000)
    (49209 / 1000) (49293 / 1000) (-138147 / 250) (399141 / 1000000) (372283 / 125) (3944393 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1846773 / 500000) (649022627 / 10000) (3944393 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1846773 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1846773 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell319 :
    ∀ t ∈ Set.Icc ((8289 / 102400) : ℝ) (41447 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175736231 / 1000000000) : ℝ) ≤ Real.exp (2 * (8289 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8289 / 102400)) (1175736231 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41447 / 512000) : ℝ)) ≤ (1175745417 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41447 / 512000)) (1175745417 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((202837217 / 3125) : ℝ) ≤ Real.exp (3 * (147743 / 40000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (147743 / 40000)) (202837217 / 3125) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8289 / 102400) : ℝ) (41447 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (147743 / 40000) (1846861 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8289 / 102400) (41447 / 512000) (1175736231 / 1000000000) (1175745417 / 1000000000) (147743 / 40000) (1846861 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8289 / 102400) (41447 / 512000) (147743 / 40000) (1846861 / 500000) (32407 / 1000) (32413 / 1000)
    (12303 / 250) (6162 / 125) (-552593 / 1000) (99779 / 250000) (1489179 / 500) (78881 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (147743 / 40000) (202837217 / 3125) (78881 / 20000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (147743 / 40000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (147743 / 40000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch015 :
    ∀ t ∈ Set.Icc ((41407 / 512000) : ℝ) (41447 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell300
      hpThetaDensityLowerExpCompact_cell301)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell302
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell303
      hpThetaDensityLowerExpCompact_cell304)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell305
      hpThetaDensityLowerExpCompact_cell306)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell307
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell308
      hpThetaDensityLowerExpCompact_cell309))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell310
      hpThetaDensityLowerExpCompact_cell311)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell312
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell313
      hpThetaDensityLowerExpCompact_cell314)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell315
      hpThetaDensityLowerExpCompact_cell316)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell317
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell318
      hpThetaDensityLowerExpCompact_cell319)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch015
end HodgeProofHP
