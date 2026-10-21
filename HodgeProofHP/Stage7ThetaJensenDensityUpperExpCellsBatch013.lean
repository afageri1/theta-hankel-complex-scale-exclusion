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
theorem hpThetaDensityUpperExpCompact_cell260 :
    ∀ t ∈ Set.Icc ((867 / 2000) : ℝ) (869 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((47595217 / 20000000) : ℝ) ≤ Real.exp (2 * (867 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (867 / 2000)) (47595217 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((869 / 2000) : ℝ)) ≤ (149032821 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (869 / 2000)) (149032821 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((5318387307593729 / 1000000) : ℝ) ≤ Real.exp (3 * (3738009 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3738009 / 500000)) (5318387307593729 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((867 / 2000) : ℝ) (869 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3738009 / 500000) (299649 / 40000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (867 / 2000) (869 / 2000) (47595217 / 20000000) (149032821 / 62500000) (3738009 / 500000) (299649 / 40000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (867 / 2000) (869 / 2000) (3738009 / 500000) (299649 / 40000) (22327 / 125) (89809 / 500)
    (885657 / 500) (1798811 / 1000) (12569497 / 1000) (21 / 500000) (50388491 / 1000) (49 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3738009 / 500000) (5318387307593729 / 1000000) (49 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3738009 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3738009 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell261 :
    ∀ t ∈ Set.Icc ((869 / 2000) : ℝ) (871 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((476905027 / 200000000) : ℝ) ≤ Real.exp (2 * (869 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (869 / 2000)) (476905027 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((871 / 2000) : ℝ)) ≤ (2389298959 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (871 / 2000)) (2389298959 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((5558315408185697 / 1000000) : ℝ) ≤ Real.exp (3 * (1498197 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1498197 / 200000)) (5558315408185697 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((869 / 2000) : ℝ) (871 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1498197 / 200000) (3753111 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (869 / 2000) (871 / 2000) (476905027 / 200000000) (2389298959 / 1000000000) (1498197 / 200000) (3753111 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (869 / 2000) (871 / 2000) (1498197 / 200000) (3753111 / 500000) (89711 / 500) (45107 / 250)
    (446227 / 250) (362511 / 200) (6364563 / 500) (1 / 25000) (12698301 / 250) (47 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1498197 / 200000) (5558315408185697 / 1000000) (47 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1498197 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1498197 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell262 :
    ∀ t ∈ Set.Icc ((871 / 2000) : ℝ) (873 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2389298957 / 1000000000) : ℝ) ≤ Real.exp (2 * (871 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (871 / 2000)) (2389298957 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((873 / 2000) : ℝ)) ≤ (1197041169 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (873 / 2000)) (1197041169 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1452374967333749 / 250000) : ℝ) ≤ Real.exp (3 * (3752991 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3752991 / 500000)) (1452374967333749 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((871 / 2000) : ℝ) (873 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3752991 / 500000) (6017 / 800) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (871 / 2000) (873 / 2000) (2389298957 / 1000000000) (1197041169 / 500000000) (3752991 / 500000) (6017 / 800) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (871 / 2000) (873 / 2000) (3752991 / 500000) (6017 / 800) (180231 / 1000) (181241 / 1000)
    (359719 / 200) (365279 / 200) (12890487 / 1000) (39 / 1000000) (25600597 / 500) (9 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3752991 / 500000) (1452374967333749 / 250000) (9 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3752991 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3752991 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell263 :
    ∀ t ∈ Set.Icc ((873 / 2000) : ℝ) (7 / 16), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2394082337 / 1000000000) : ℝ) ≤ Real.exp (2 * (873 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (873 / 2000)) (2394082337 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((7 / 16) : ℝ)) ≤ (1199437647 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (7 / 16)) (1199437647 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6072486113752851 / 1000000) : ℝ) ≤ Real.exp (3 * (7521009 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (7521009 / 1000000)) (6072486113752851 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((873 / 2000) : ℝ) (7 / 16),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (7521009 / 1000000) (7536307 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (873 / 2000) (7 / 16) (2394082337 / 1000000000) (1199437647 / 500000000) (7521009 / 1000000) (7536307 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (873 / 2000) (7 / 16) (7521009 / 1000000) (7536307 / 1000000) (45261 / 250) (91029 / 500)
    (1812379 / 1000) (184033 / 100) (13053537 / 1000) (37 / 1000000) (51612431 / 1000) (43 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (7521009 / 1000000) (6072486113752851 / 1000000) (43 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7521009 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7521009 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell264 :
    ∀ t ∈ Set.Icc ((7 / 16) : ℝ) (877 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2398875293 / 1000000000) : ℝ) ≤ Real.exp (2 * (7 / 16)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (7 / 16)) (2398875293 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((877 / 2000) : ℝ)) ≤ (1201838923 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (877 / 2000)) (1201838923 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6347846708383607 / 1000000) : ℝ) ≤ Real.exp (3 * (3768033 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3768033 / 500000)) (6347846708383607 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((7 / 16) : ℝ) (877 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3768033 / 500000) (1510279 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (7 / 16) (877 / 2000) (2398875293 / 1000000000) (1201838923 / 500000000) (3768033 / 500000) (1510279 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (7 / 16) (877 / 2000) (3768033 / 500000) (1510279 / 200000) (9093 / 50) (91439 / 500)
    (1826257 / 1000) (927181 / 500) (264367 / 20) (9 / 250000) (10405399 / 200) (41 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3768033 / 500000) (6347846708383607 / 1000000) (41 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3768033 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3768033 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell265 :
    ∀ t ∈ Set.Icc ((877 / 2000) : ℝ) (879 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((480735569 / 200000000) : ℝ) ≤ Real.exp (2 * (877 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (877 / 2000)) (480735569 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((879 / 2000) : ℝ)) ≤ (602122503 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (879 / 2000)) (602122503 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3318091372724187 / 500000) : ℝ) ≤ Real.exp (3 * (7551153 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (7551153 / 1000000)) (3318091372724187 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((877 / 2000) : ℝ) (879 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (7551153 / 1000000) (7566513 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (877 / 2000) (879 / 2000) (480735569 / 200000000) (602122503 / 250000000) (7551153 / 1000000) (7566513 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (877 / 2000) (879 / 2000) (7551153 / 1000000) (7566513 / 1000000) (4567 / 25) (91851 / 500)
    (230029 / 125) (467123 / 250) (13384913 / 1000) (17 / 500000) (52444883 / 1000) (39 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (7551153 / 1000000) (3318091372724187 / 500000) (39 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7551153 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7551153 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell266 :
    ∀ t ∈ Set.Icc ((879 / 2000) : ℝ) (881 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2408490011 / 1000000000) : ℝ) ≤ Real.exp (2 * (879 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (879 / 2000)) (2408490011 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((881 / 2000) : ℝ)) ≤ (603327953 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (881 / 2000)) (603327953 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((277525828519321 / 40000) : ℝ) ≤ Real.exp (3 * (7566271 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (7566271 / 1000000)) (277525828519321 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((879 / 2000) : ℝ) (881 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (7566271 / 1000000) (7581661 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (879 / 2000) (881 / 2000) (2408490011 / 1000000000) (603327953 / 250000000) (7566271 / 1000000) (7581661 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (879 / 2000) (881 / 2000) (7566271 / 1000000) (7581661 / 1000000) (183503 / 1000) (184529 / 1000)
    (370861 / 200) (1882719 / 1000) (1694153 / 125) (33 / 1000000) (1321653 / 25) (37 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (7566271 / 1000000) (277525828519321 / 40000) (37 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7566271 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7566271 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell267 :
    ∀ t ∈ Set.Icc ((881 / 2000) : ℝ) (883 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2413311811 / 1000000000) : ℝ) ≤ Real.exp (2 * (881 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (881 / 2000)) (2413311811 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((883 / 2000) : ℝ)) ≤ (1209071633 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (883 / 2000)) (1209071633 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((90679745193807 / 12500) : ℝ) ≤ Real.exp (3 * (7581419 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (7581419 / 1000000)) (90679745193807 / 12500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((881 / 2000) : ℝ) (883 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (7581419 / 1000000) (7596839 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (881 / 2000) (883 / 2000) (2413311811 / 1000000000) (1209071633 / 500000000) (7581419 / 1000000) (7596839 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (881 / 2000) (883 / 2000) (7581419 / 1000000) (7596839 / 1000000) (18433 / 100) (4634 / 25)
    (74739 / 40) (474261 / 250) (13723317 / 1000) (1 / 31250) (53290731 / 1000) (9 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (7581419 / 1000000) (90679745193807 / 12500) (9 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7581419 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7581419 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell268 :
    ∀ t ∈ Set.Icc ((883 / 2000) : ℝ) (177 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((75566977 / 31250000) : ℝ) ≤ Real.exp (2 * (883 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (883 / 2000)) (75566977 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((177 / 400) : ℝ)) ≤ (302873049 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (177 / 400)) (302873049 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((948197533950799 / 125000) : ℝ) ≤ Real.exp (3 * (7596597 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (7596597 / 1000000)) (948197533950799 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((883 / 2000) : ℝ) (177 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (7596597 / 1000000) (475753 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (883 / 2000) (177 / 400) (75566977 / 31250000) (302873049 / 125000000) (7596597 / 1000000) (475753 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (883 / 2000) (177 / 400) (7596597 / 1000000) (475753 / 62500) (4629 / 25) (93097 / 500)
    (1882743 / 1000) (1911469 / 1000) (347381 / 25) (31 / 1000000) (5371877 / 100) (17 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (7596597 / 1000000) (948197533950799 / 125000) (17 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7596597 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7596597 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell269 :
    ∀ t ∈ Set.Icc ((177 / 400) : ℝ) (887 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((242298439 / 100000000) : ℝ) ≤ Real.exp (2 * (177 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (177 / 400)) (242298439 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((887 / 2000) : ℝ)) ≤ (242783521 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (887 / 2000)) (242783521 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3966239155876033 / 500000) : ℝ) ≤ Real.exp (3 * (1522361 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1522361 / 200000)) (3966239155876033 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((177 / 400) : ℝ) (887 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1522361 / 200000) (953411 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (177 / 400) (887 / 2000) (242298439 / 100000000) (242783521 / 100000000) (1522361 / 200000) (953411 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (177 / 400) (887 / 2000) (1522361 / 200000) (953411 / 125000) (92997 / 500) (23379 / 125)
    (1897109 / 1000) (962997 / 500) (14069009 / 1000) (3 / 100000) (54150263 / 1000) (33 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1522361 / 200000) (3966239155876033 / 500000) (33 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1522361 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1522361 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell270 :
    ∀ t ∈ Set.Icc ((887 / 2000) : ℝ) (889 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((303479401 / 125000000) : ℝ) ≤ Real.exp (2 * (887 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (887 / 2000)) (303479401 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((889 / 2000) : ℝ)) ≤ (2432695739 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (889 / 2000)) (2432695739 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4147932668367501 / 500000) : ℝ) ≤ Real.exp (3 * (1906761 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1906761 / 250000)) (4147932668367501 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((887 / 2000) : ℝ) (889 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1906761 / 250000) (7642557 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (887 / 2000) (889 / 2000) (303479401 / 125000000) (2432695739 / 1000000000) (1906761 / 250000) (7642557 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (887 / 2000) (889 / 2000) (1906761 / 250000) (7642557 / 1000000) (186831 / 1000) (187873 / 1000)
    (238947 / 125) (970309 / 500) (14244561 / 1000) (7 / 250000) (27292589 / 500) (31 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1906761 / 250000) (4147932668367501 / 500000) (31 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1906761 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1906761 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell271 :
    ∀ t ∈ Set.Icc ((889 / 2000) : ℝ) (891 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1216347869 / 500000000) : ℝ) ≤ Real.exp (2 * (889 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (889 / 2000)) (1216347869 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((891 / 2000) : ℝ)) ≤ (2437565999 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (891 / 2000)) (2437565999 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4338262434727583 / 500000) : ℝ) ≤ Real.exp (3 * (7642313 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (7642313 / 1000000)) (4338262434727583 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((889 / 2000) : ℝ) (891 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (7642313 / 1000000) (3828929 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (889 / 2000) (891 / 2000) (1216347869 / 500000000) (2437565999 / 1000000000) (7642313 / 1000000) (3828929 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (889 / 2000) (891 / 2000) (7642313 / 1000000) (3828929 / 500000) (23459 / 125) (94359 / 500)
    (963071 / 500) (391069 / 200) (576881 / 40) (7 / 250000) (13755907 / 250) (3 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (7642313 / 1000000) (4338262434727583 / 500000) (3 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7642313 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7642313 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell272 :
    ∀ t ∈ Set.Icc ((891 / 2000) : ℝ) (893 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1218782999 / 500000000) : ℝ) ≤ Real.exp (2 * (891 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (891 / 2000)) (1218782999 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((893 / 2000) : ℝ)) ≤ (244244601 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (893 / 2000)) (244244601 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2268832458036867 / 250000) : ℝ) ≤ Real.exp (3 * (7657613 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (7657613 / 1000000)) (2268832458036867 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((891 / 2000) : ℝ) (893 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (7657613 / 1000000) (7673189 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (891 / 2000) (893 / 2000) (1218782999 / 500000000) (244244601 / 100000000) (7657613 / 1000000) (7673189 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (891 / 2000) (893 / 2000) (7657613 / 1000000) (7673189 / 1000000) (188517 / 1000) (94783 / 500)
    (1940809 / 1000) (1970173 / 1000) (14601337 / 1000) (27 / 1000000) (55465581 / 1000) (29 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (7657613 / 1000000) (2268832458036867 / 250000) (29 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7657613 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7657613 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell273 :
    ∀ t ∈ Set.Icc ((893 / 2000) : ℝ) (179 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((305305751 / 125000000) : ℝ) ≤ Real.exp (2 * (893 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (893 / 2000)) (305305751 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((179 / 400) : ℝ)) ≤ (244733579 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (179 / 400)) (244733579 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1898634531732827 / 200000) : ℝ) ≤ Real.exp (3 * (479559 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (479559 / 62500)) (1898634531732827 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((893 / 2000) : ℝ) (179 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (479559 / 62500) (7688551 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (893 / 2000) (179 / 400) (305305751 / 125000000) (244733579 / 100000000) (479559 / 62500) (7688551 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (893 / 2000) (179 / 400) (479559 / 62500) (7688551 / 1000000) (47341 / 250) (95209 / 500)
    (1955579 / 1000) (1985103 / 1000) (1847818 / 125) (1 / 40000) (55911093 / 1000) (27 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (479559 / 62500) (1898634531732827 / 200000) (27 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (479559 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (479559 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell274 :
    ∀ t ∈ Set.Icc ((179 / 400) : ℝ) (897 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((611833947 / 250000000) : ℝ) ≤ Real.exp (2 * (179 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (179 / 400)) (611833947 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((897 / 2000) : ℝ)) ≤ (2452235359 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (897 / 2000)) (2452235359 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4965480839207227 / 500000) : ℝ) ≤ Real.exp (3 * (1537661 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1537661 / 200000)) (4965480839207227 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((179 / 400) : ℝ) (897 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1537661 / 200000) (7703943 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (179 / 400) (897 / 2000) (611833947 / 250000000) (2452235359 / 1000000000) (1537661 / 200000) (7703943 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (179 / 400) (897 / 2000) (1537661 / 200000) (7703943 / 1000000) (23777 / 125) (95637 / 500)
    (39409 / 20) (250017 / 125) (14965653 / 1000) (3 / 125000) (28180081 / 500) (13 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1537661 / 200000) (4965480839207227 / 500000) (13 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1537661 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1537661 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell275 :
    ∀ t ∈ Set.Icc ((897 / 2000) : ℝ) (899 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1226117679 / 500000000) : ℝ) ≤ Real.exp (2 * (897 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (897 / 2000)) (1226117679 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((899 / 2000) : ℝ)) ≤ (1228572369 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (899 / 2000)) (1228572369 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((10389708194197533 / 1000000) : ℝ) ≤ Real.exp (3 * (7703697 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (7703697 / 1000000)) (10389708194197533 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((897 / 2000) : ℝ) (899 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (7703697 / 1000000) (3859683 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (897 / 2000) (899 / 2000) (1226117679 / 500000000) (1228572369 / 500000000) (7703697 / 1000000) (3859683 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (897 / 2000) (899 / 2000) (7703697 / 1000000) (3859683 / 500000) (191071 / 1000) (192133 / 1000)
    (248178 / 125) (2015273 / 1000) (7575347 / 500) (3 / 125000) (28406421 / 500) (1 / 40000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (7703697 / 1000000) (10389708194197533 / 1000000) (1 / 40000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7703697 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7703697 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell276 :
    ∀ t ∈ Set.Icc ((899 / 2000) : ℝ) (901 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((76785773 / 31250000) : ℝ) ≤ Real.exp (2 * (899 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (899 / 2000)) (76785773 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((901 / 2000) : ℝ)) ≤ (492412789 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (901 / 2000)) (492412789 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((10870446648356617 / 1000000) : ℝ) ≤ Real.exp (3 * (96489 / 12500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (96489 / 12500)) (10870446648356617 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((899 / 2000) : ℝ) (901 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (96489 / 12500) (7734821 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (899 / 2000) (901 / 2000) (76785773 / 31250000) (492412789 / 200000000) (96489 / 12500) (7734821 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (899 / 2000) (901 / 2000) (96489 / 12500) (7734821 / 1000000) (19193 / 100) (48249 / 250)
    (2000501 / 1000) (507629 / 250) (3067543 / 200) (23 / 1000000) (7158649 / 125) (3 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (96489 / 12500) (10870446648356617 / 1000000) (3 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (96489 / 12500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (96489 / 12500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell277 :
    ∀ t ∈ Set.Icc ((901 / 2000) : ℝ) (903 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2462063943 / 1000000000) : ℝ) ≤ Real.exp (2 * (901 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (901 / 2000)) (2462063943 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((903 / 2000) : ℝ)) ≤ (2466993 / 1000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (903 / 2000)) (2466993 / 1000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((11374230505750221 / 1000000) : ℝ) ≤ Real.exp (3 * (7734573 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (7734573 / 1000000)) (11374230505750221 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((901 / 2000) : ℝ) (903 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (7734573 / 1000000) (3875153 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (901 / 2000) (903 / 2000) (2462063943 / 1000000000) (2466993 / 1000000) (7734573 / 1000000) (3875153 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (901 / 2000) (903 / 2000) (7734573 / 1000000) (3875153 / 500000) (24099 / 125) (96931 / 500)
    (1007841 / 500) (2045863 / 1000) (15526691 / 1000) (11 / 500000) (2886459 / 50) (23 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (7734573 / 1000000) (11374230505750221 / 1000000) (23 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7734573 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7734573 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell278 :
    ∀ t ∈ Set.Icc ((903 / 2000) : ℝ) (181 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2466992999 / 1000000000) : ℝ) ≤ Real.exp (2 * (903 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (903 / 2000)) (2466992999 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((181 / 400) : ℝ)) ≤ (617982981 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (181 / 400)) (617982981 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((148778334748943 / 12500) : ℝ) ≤ Real.exp (3 * (3875029 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3875029 / 500000)) (148778334748943 / 12500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((903 / 2000) : ℝ) (181 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3875029 / 500000) (3882911 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (903 / 2000) (181 / 400) (2466992999 / 1000000000) (617982981 / 250000000) (3875029 / 500000) (3882911 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (903 / 2000) (181 / 400) (3875029 / 500000) (3882911 / 500000) (96829 / 500) (48683 / 250)
    (2030969 / 1000) (412263 / 200) (1964704 / 125) (21 / 1000000) (29096431 / 500) (11 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3875029 / 500000) (148778334748943 / 12500) (11 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3875029 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3875029 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell279 :
    ∀ t ∈ Set.Icc ((181 / 400) : ℝ) (907 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1235965961 / 500000000) : ℝ) ≤ Real.exp (2 * (181 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (181 / 400)) (1235965961 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((907 / 2000) : ℝ)) ≤ (495376147 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (907 / 2000)) (495376147 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6227861689006477 / 500000) : ℝ) ≤ Real.exp (3 * (3882787 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3882787 / 500000)) (6227861689006477 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((181 / 400) : ℝ) (907 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3882787 / 500000) (7781369 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (181 / 400) (907 / 2000) (1235965961 / 500000000) (495376147 / 200000000) (3882787 / 500000) (7781369 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (181 / 400) (907 / 2000) (3882787 / 500000) (7781369 / 1000000) (24316 / 125) (97803 / 500)
    (1023181 / 500) (1038437 / 500) (15910577 / 1000) (1 / 50000) (29330133 / 500) (21 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3882787 / 500000) (6227861689006477 / 500000) (21 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3882787 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3882787 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityUpperExpCompact_cellsBatch013 :
    ∀ t ∈ Set.Icc ((867 / 2000) : ℝ) (907 / 2000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell260
      hpThetaDensityUpperExpCompact_cell261)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell262
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell263
      hpThetaDensityUpperExpCompact_cell264)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell265
      hpThetaDensityUpperExpCompact_cell266)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell267
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell268
      hpThetaDensityUpperExpCompact_cell269))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell270
      hpThetaDensityUpperExpCompact_cell271)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell272
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell273
      hpThetaDensityUpperExpCompact_cell274)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell275
      hpThetaDensityUpperExpCompact_cell276)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell277
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell278
      hpThetaDensityUpperExpCompact_cell279)))))

#print axioms hpThetaDensityUpperExpCompact_cellsBatch013
end HodgeProofHP
