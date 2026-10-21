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
theorem hpThetaDensityUpperExpCompact_cell000 :
    ∀ t ∈ Set.Icc ((1 / 5) : ℝ) (401 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1491824697 / 1000000000) : ℝ) ≤ Real.exp (2 * (1 / 5)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1 / 5)) (1491824697 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((401 / 2000) : ℝ)) ≤ (1493317269 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (401 / 2000)) (1493317269 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1276551951797 / 1000000) : ℝ) ≤ Real.exp (3 * (4686567 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4686567 / 1000000)) (1276551951797 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1 / 5) : ℝ) (401 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4686567 / 1000000) (2345703 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1 / 5) (401 / 2000) (1491824697 / 1000000000) (1493317269 / 1000000000) (4686567 / 1000000) (2345703 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1 / 5) (401 / 2000) (4686567 / 1000000) (2345703 / 500000) (59707 / 1000) (29959 / 500)
    (116751 / 500) (23749 / 100) (-322429 / 1000) (2079 / 50000) (3875271 / 500) (200541 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4686567 / 1000000) (1276551951797 / 1000000) (200541 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4686567 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4686567 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell001 :
    ∀ t ∈ Set.Icc ((401 / 2000) : ℝ) (201 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((373329317 / 250000000) : ℝ) ≤ Real.exp (2 * (401 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (401 / 2000)) (373329317 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((201 / 1000) : ℝ)) ≤ (1494811333 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (201 / 1000)) (1494811333 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1294635428343 / 1000000) : ℝ) ≤ Real.exp (3 * (586407 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (586407 / 125000)) (1294635428343 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((401 / 2000) : ℝ) (201 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (586407 / 125000) (46961 / 10000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (401 / 2000) (201 / 1000) (373329317 / 250000000) (1494811333 / 1000000000) (586407 / 125000) (46961 / 10000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (401 / 2000) (201 / 1000) (586407 / 125000) (46961 / 10000) (29927 / 500) (30033 / 500)
    (9389 / 40) (59681 / 250) (-318907 / 1000) (20561 / 500000) (972701 / 125) (9887 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (586407 / 125000) (1294635428343 / 1000000) (9887 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (586407 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (586407 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell002 :
    ∀ t ∈ Set.Icc ((201 / 1000) : ℝ) (403 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((373702833 / 250000000) : ℝ) ≤ Real.exp (2 * (201 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (201 / 1000)) (373702833 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((403 / 2000) : ℝ)) ≤ (374076723 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (403 / 2000)) (374076723 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1312990816663 / 1000000) : ℝ) ≤ Real.exp (3 * (4695949 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4695949 / 1000000)) (1312990816663 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((201 / 1000) : ℝ) (403 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4695949 / 1000000) (2350399 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (201 / 1000) (403 / 2000) (373702833 / 250000000) (374076723 / 250000000) (4695949 / 1000000) (2350399 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (201 / 1000) (403 / 2000) (4695949 / 1000000) (2350399 / 500000) (30001 / 500) (12043 / 200)
    (29494 / 125) (239961 / 1000) (-315351 / 1000) (40669 / 1000000) (3906397 / 500) (7799 / 40000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4695949 / 1000000) (1312990816663 / 1000000) (7799 / 40000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4695949 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4695949 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell003 :
    ∀ t ∈ Set.Icc ((403 / 2000) : ℝ) (101 / 500), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1496306891 / 1000000000) : ℝ) ≤ Real.exp (2 * (403 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (403 / 2000)) (1496306891 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((101 / 500) : ℝ)) ≤ (1497803947 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (101 / 500)) (1497803947 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1331630404479 / 1000000) : ℝ) ≤ Real.exp (3 * (587581 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (587581 / 125000)) (1331630404479 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((403 / 2000) : ℝ) (101 / 500),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (587581 / 125000) (4705501 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (403 / 2000) (101 / 500) (1496306891 / 1000000000) (1497803947 / 1000000000) (587581 / 125000) (4705501 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (403 / 2000) (101 / 500) (587581 / 125000) (4705501 / 1000000) (60151 / 1000) (15091 / 250)
    (47437 / 200) (60301 / 250) (-311767 / 1000) (2011 / 50000) (7844107 / 1000) (96123 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (587581 / 125000) (1331630404479 / 1000000) (96123 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (587581 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (587581 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell004 :
    ∀ t ∈ Set.Icc ((101 / 500) : ℝ) (81 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((748901973 / 500000000) : ℝ) ≤ Real.exp (2 * (101 / 500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (101 / 500)) (748901973 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((81 / 400) : ℝ)) ≤ (1499302501 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (81 / 400)) (1499302501 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1350550798551 / 1000000) : ℝ) ≤ Real.exp (3 * (4705351 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4705351 / 1000000)) (1350550798551 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((101 / 500) : ℝ) (81 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4705351 / 1000000) (4710209 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (101 / 500) (81 / 400) (748901973 / 500000000) (1499302501 / 1000000000) (4705351 / 1000000) (4710209 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (101 / 500) (81 / 400) (4705351 / 1000000) (4710209 / 1000000) (603 / 10) (60513 / 1000)
    (119211 / 500) (60613 / 250) (-15407 / 50) (1243 / 31250) (7875547 / 1000) (189553 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4705351 / 1000000) (1350550798551 / 1000000) (189553 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4705351 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4705351 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell005 :
    ∀ t ∈ Set.Icc ((81 / 400) : ℝ) (203 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((599721 / 400000) : ℝ) ≤ Real.exp (2 * (81 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (81 / 400)) (599721 / 400000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((203 / 1000) : ℝ)) ≤ (1500802553 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (203 / 1000)) (1500802553 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((684878222711 / 500000) : ℝ) ≤ Real.exp (3 * (2355029 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2355029 / 500000)) (684878222711 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((81 / 400) : ℝ) (203 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2355029 / 500000) (2357461 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (81 / 400) (203 / 1000) (599721 / 400000) (1500802553 / 1000000000) (2355029 / 500000) (2357461 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (81 / 400) (203 / 1000) (2355029 / 500000) (2357461 / 500000) (60449 / 1000) (30331 / 500)
    (239663 / 1000) (48741 / 200) (-30447 / 100) (4917 / 125000) (1581423 / 200) (37379 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2355029 / 500000) (684878222711 / 500000) (37379 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2355029 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2355029 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell006 :
    ∀ t ∈ Set.Icc ((203 / 1000) : ℝ) (407 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((187600319 / 125000000) : ℝ) ≤ Real.exp (2 * (203 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (203 / 1000)) (187600319 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((407 / 2000) : ℝ)) ≤ (751152053 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (407 / 2000)) (751152053 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((694630100179 / 500000) : ℝ) ≤ Real.exp (3 * (4714771 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4714771 / 1000000)) (694630100179 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((203 / 1000) : ℝ) (407 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4714771 / 1000000) (4719639 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (203 / 1000) (407 / 2000) (187600319 / 125000000) (751152053 / 500000000) (4714771 / 1000000) (4719639 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (203 / 1000) (407 / 2000) (4714771 / 1000000) (4719639 / 1000000) (30299 / 500) (15203 / 250)
    (240911 / 1000) (122481 / 500) (-15039 / 50) (389 / 10000) (1587761 / 200) (184271 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4714771 / 1000000) (694630100179 / 500000) (184271 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4714771 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4714771 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell007 :
    ∀ t ∈ Set.Icc ((407 / 2000) : ℝ) (51 / 250), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((300460821 / 200000000) : ℝ) ≤ Real.exp (2 * (407 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (407 / 2000)) (300460821 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((51 / 250) : ℝ)) ≤ (751903581 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (51 / 250)) (751903581 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1409058560529 / 1000000) : ℝ) ≤ Real.exp (3 * (73742 / 15625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (73742 / 15625)) (1409058560529 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((407 / 2000) : ℝ) (51 / 250),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (73742 / 15625) (4724361 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (407 / 2000) (51 / 250) (300460821 / 200000000) (751903581 / 500000000) (73742 / 15625) (4724361 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (407 / 2000) (51 / 250) (73742 / 15625) (4724361 / 1000000) (15187 / 250) (30481 / 500)
    (242163 / 1000) (9849 / 40) (-148523 / 500) (38469 / 1000000) (996328 / 125) (90841 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (73742 / 15625) (1409058560529 / 1000000) (90841 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (73742 / 15625)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (73742 / 15625)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell008 :
    ∀ t ∈ Set.Icc ((51 / 250) : ℝ) (409 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1503807161 / 1000000000) : ℝ) ≤ Real.exp (2 * (51 / 250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (51 / 250)) (1503807161 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((409 / 2000) : ℝ)) ≤ (1505311721 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (409 / 2000)) (1505311721 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((357290122387 / 250000) : ℝ) ≤ Real.exp (3 * (472421 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (472421 / 100000)) (357290122387 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((51 / 250) : ℝ) (409 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (472421 / 100000) (73892 / 15625) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (51 / 250) (409 / 2000) (1503807161 / 1000000000) (1505311721 / 1000000000) (472421 / 100000) (73892 / 15625) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (51 / 250) (409 / 2000) (472421 / 100000) (73892 / 15625) (30449 / 500) (7639 / 125)
    (12171 / 50) (247493 / 1000) (-73319 / 250) (19021 / 500000) (2000643 / 250) (179127 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (472421 / 100000) (357290122387 / 250000) (179127 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (472421 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (472421 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell009 :
    ∀ t ∈ Set.Icc ((409 / 2000) : ℝ) (41 / 200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((37632793 / 25000000) : ℝ) ≤ Real.exp (2 * (409 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (409 / 2000)) (37632793 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41 / 200) : ℝ)) ≤ (753408893 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41 / 200)) (753408893 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1449566576349 / 1000000) : ℝ) ≤ Real.exp (3 * (591117 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (591117 / 125000)) (1449566576349 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((409 / 2000) : ℝ) (41 / 200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (591117 / 125000) (4733819 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (409 / 2000) (41 / 200) (37632793 / 25000000) (753408893 / 500000000) (591117 / 125000) (4733819 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (409 / 2000) (41 / 200) (591117 / 125000) (4733819 / 1000000) (7631 / 125) (61263 / 1000)
    (122341 / 500) (124383 / 500) (-289471 / 1000) (37619 / 1000000) (8034643 / 1000) (35321 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (591117 / 125000) (1449566576349 / 1000000) (35321 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (591117 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (591117 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell010 :
    ∀ t ∈ Set.Icc ((41 / 200) : ℝ) (411 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((301363557 / 200000000) : ℝ) ≤ Real.exp (2 * (41 / 200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41 / 200)) (301363557 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((411 / 2000) : ℝ)) ≤ (1508325357 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (411 / 2000)) (1508325357 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1470290477691 / 1000000) : ℝ) ≤ Real.exp (3 * (1183417 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1183417 / 250000)) (1470290477691 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41 / 200) : ℝ) (411 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1183417 / 250000) (947711 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41 / 200) (411 / 2000) (301363557 / 200000000) (1508325357 / 1000000000) (1183417 / 250000) (947711 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41 / 200) (411 / 2000) (1183417 / 250000) (947711 / 200000) (61199 / 1000) (30707 / 500)
    (245949 / 1000) (250043 / 1000) (-71409 / 250) (93 / 2500) (1613369 / 200) (43529 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1183417 / 250000) (1470290477691 / 1000000) (43529 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1183417 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1183417 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell011 :
    ∀ t ∈ Set.Icc ((411 / 2000) : ℝ) (103 / 500), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((377081339 / 250000000) : ℝ) ≤ Real.exp (2 * (411 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (411 / 2000)) (377081339 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((103 / 500) : ℝ)) ≤ (1509834437 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (103 / 500)) (1509834437 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1491328540301 / 1000000) : ℝ) ≤ Real.exp (3 * (1184601 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1184601 / 250000)) (1491328540301 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((411 / 2000) : ℝ) (103 / 500),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1184601 / 250000) (74114 / 15625) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (411 / 2000) (103 / 500) (377081339 / 250000000) (1509834437 / 1000000000) (1184601 / 250000) (74114 / 15625) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (411 / 2000) (103 / 500) (1184601 / 250000) (74114 / 15625) (1227 / 20) (30783 / 500)
    (247221 / 1000) (125663 / 500) (-70439 / 250) (18393 / 500000) (4049589 / 500) (8583 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1184601 / 250000) (1491328540301 / 1000000) (8583 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1184601 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1184601 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell012 :
    ∀ t ∈ Set.Icc ((103 / 500) : ℝ) (413 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((377458609 / 250000000) : ℝ) ≤ Real.exp (2 * (103 / 500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (103 / 500)) (377458609 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((413 / 2000) : ℝ)) ≤ (755672513 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (413 / 2000)) (755672513 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((151268576723 / 100000) : ℝ) ≤ Real.exp (3 * (592893 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (592893 / 125000)) (151268576723 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((103 / 500) : ℝ) (413 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (592893 / 125000) (2374021 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (103 / 500) (413 / 2000) (377458609 / 250000000) (755672513 / 500000000) (592893 / 125000) (2374021 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (103 / 500) (413 / 2000) (592893 / 125000) (2374021 / 500000) (61501 / 1000) (61717 / 1000)
    (248497 / 1000) (126307 / 500) (-34729 / 125) (291 / 8000) (8131641 / 1000) (42309 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (592893 / 125000) (151268576723 / 100000) (42309 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (592893 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (592893 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell013 :
    ∀ t ∈ Set.Icc ((413 / 2000) : ℝ) (207 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((60453801 / 40000000) : ℝ) ≤ Real.exp (2 * (413 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (413 / 2000)) (60453801 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((207 / 1000) : ℝ)) ≤ (1512857127 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (207 / 1000)) (1512857127 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((191797056313 / 125000) : ℝ) ≤ Real.exp (3 * (474789 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (474789 / 100000)) (191797056313 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((413 / 2000) : ℝ) (207 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (474789 / 100000) (594099 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (413 / 2000) (207 / 1000) (60453801 / 40000000) (1512857127 / 1000000000) (474789 / 100000) (594099 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (413 / 2000) (207 / 1000) (474789 / 100000) (594099 / 125000) (61653 / 1000) (61869 / 1000)
    (12489 / 50) (126953 / 500) (-273887 / 1000) (35969 / 1000000) (816423 / 100) (41711 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (474789 / 100000) (191797056313 / 125000) (41711 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (474789 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (474789 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell014 :
    ∀ t ∈ Set.Icc ((207 / 1000) : ℝ) (83 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((756428563 / 500000000) : ℝ) ≤ Real.exp (2 * (207 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (207 / 1000)) (756428563 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((83 / 400) : ℝ)) ≤ (1514370741 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (83 / 400)) (1514370741 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1556396819291 / 1000000) : ℝ) ≤ Real.exp (3 * (14852 / 3125)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (14852 / 3125)) (1556396819291 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((207 / 1000) : ℝ) (83 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (14852 / 3125) (1189387 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (207 / 1000) (83 / 400) (756428563 / 500000000) (1514370741 / 1000000000) (14852 / 3125) (1189387 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (207 / 1000) (83 / 400) (14852 / 3125) (1189387 / 250000) (12361 / 200) (31011 / 500)
    (251067 / 1000) (51041 / 200) (-269887 / 1000) (17783 / 500000) (4098479 / 500) (164483 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (14852 / 3125) (1556396819291 / 1000000) (164483 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (14852 / 3125)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (14852 / 3125)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell015 :
    ∀ t ∈ Set.Icc ((83 / 400) : ℝ) (26 / 125), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((75718537 / 50000000) : ℝ) ≤ Real.exp (2 * (83 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (83 / 400)) (75718537 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((26 / 125) : ℝ)) ≤ (1515885869 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (26 / 125)) (1515885869 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1578756872531 / 1000000) : ℝ) ≤ Real.exp (3 * (951479 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (951479 / 200000)) (1578756872531 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((83 / 400) : ℝ) (26 / 125),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (951479 / 200000) (1190577 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (83 / 400) (26 / 125) (75718537 / 50000000) (1515885869 / 1000000000) (951479 / 200000) (1190577 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (83 / 400) (26 / 125) (951479 / 200000) (1190577 / 250000) (61957 / 1000) (31087 / 500)
    (252359 / 1000) (64127 / 250) (-265859 / 1000) (1099 / 31250) (2057453 / 250) (162153 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (951479 / 200000) (1578756872531 / 1000000) (162153 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (951479 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (951479 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell016 :
    ∀ t ∈ Set.Icc ((26 / 125) : ℝ) (417 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((378971467 / 250000000) : ℝ) ≤ Real.exp (2 * (26 / 125)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (26 / 125)) (378971467 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((417 / 2000) : ℝ)) ≤ (1517402513 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (417 / 2000)) (1517402513 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1601462165087 / 1000000) : ℝ) ≤ Real.exp (3 * (952431 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (952431 / 200000)) (1601462165087 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((26 / 125) : ℝ) (417 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (952431 / 200000) (148971 / 31250) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (26 / 125) (417 / 2000) (378971467 / 250000000) (1517402513 / 1000000000) (952431 / 200000) (148971 / 31250) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (26 / 125) (417 / 2000) (952431 / 200000) (148971 / 31250) (6211 / 100) (62327 / 1000)
    (31707 / 125) (32227 / 125) (-1309 / 5) (17387 / 500000) (8262793 / 1000) (79927 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (952431 / 200000) (1601462165087 / 1000000) (79927 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (952431 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (952431 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell017 :
    ∀ t ∈ Set.Icc ((417 / 2000) : ℝ) (209 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((94837657 / 62500000) : ℝ) ≤ Real.exp (2 * (417 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (417 / 2000)) (94837657 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((209 / 1000) : ℝ)) ≤ (60756827 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (209 / 1000)) (60756827 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((812256736987 / 500000) : ℝ) ≤ Real.exp (3 * (4766919 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4766919 / 1000000)) (812256736987 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((417 / 2000) : ℝ) (209 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4766919 / 1000000) (2385921 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (417 / 2000) (209 / 1000) (94837657 / 62500000) (60756827 / 40000000) (4766919 / 1000000) (2385921 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (417 / 2000) (209 / 1000) (4766919 / 1000000) (2385921 / 500000) (62263 / 1000) (62481 / 1000)
    (127479 / 500) (25913 / 100) (-257687 / 1000) (34383 / 1000000) (4147957 / 500) (78793 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4766919 / 1000000) (812256736987 / 500000) (78793 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4766919 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4766919 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell018 :
    ∀ t ∈ Set.Icc ((209 / 1000) : ℝ) (419 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((759460337 / 500000000) : ℝ) ≤ Real.exp (2 * (209 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (209 / 1000)) (759460337 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((419 / 2000) : ℝ)) ≤ (304088071 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (419 / 2000)) (304088071 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1647926223079 / 1000000) : ℝ) ≤ Real.exp (3 * (4771689 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4771689 / 1000000)) (1647926223079 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((209 / 1000) : ℝ) (419 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4771689 / 1000000) (597077 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (209 / 1000) (419 / 2000) (759460337 / 500000000) (304088071 / 200000000) (4771689 / 1000000) (597077 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (209 / 1000) (419 / 2000) (4771689 / 1000000) (597077 / 125000) (7802 / 125) (12527 / 200)
    (128133 / 500) (32556 / 125) (-31694 / 125) (8499 / 250000) (4164581 / 500) (155347 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4771689 / 1000000) (1647926223079 / 1000000) (155347 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4771689 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4771689 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell019 :
    ∀ t ∈ Set.Icc ((419 / 2000) : ℝ) (21 / 100), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((760220177 / 500000000) : ℝ) ≤ Real.exp (2 * (419 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (419 / 2000)) (760220177 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((21 / 100) : ℝ)) ≤ (380490389 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (21 / 100)) (380490389 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((334339287963 / 200000) : ℝ) ≤ Real.exp (3 * (4776463 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4776463 / 1000000)) (334339287963 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((419 / 2000) : ℝ) (21 / 100),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4776463 / 1000000) (956279 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (419 / 2000) (21 / 100) (760220177 / 500000000) (380490389 / 250000000) (4776463 / 1000000) (956279 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (419 / 2000) (21 / 100) (4776463 / 1000000) (956279 / 200000) (6257 / 100) (62789 / 1000)
    (257579 / 1000) (261771 / 1000) (-249371 / 1000) (16807 / 500000) (4181273 / 500) (76569 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4776463 / 1000000) (334339287963 / 200000) (76569 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4776463 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4776463 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityUpperExpCompact_cellsBatch000 :
    ∀ t ∈ Set.Icc ((1 / 5) : ℝ) (21 / 100),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell000
      hpThetaDensityUpperExpCompact_cell001)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell002
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell003
      hpThetaDensityUpperExpCompact_cell004)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell005
      hpThetaDensityUpperExpCompact_cell006)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell007
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell008
      hpThetaDensityUpperExpCompact_cell009))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell010
      hpThetaDensityUpperExpCompact_cell011)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell012
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell013
      hpThetaDensityUpperExpCompact_cell014)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell015
      hpThetaDensityUpperExpCompact_cell016)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell017
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell018
      hpThetaDensityUpperExpCompact_cell019)))))

#print axioms hpThetaDensityUpperExpCompact_cellsBatch000
end HodgeProofHP
