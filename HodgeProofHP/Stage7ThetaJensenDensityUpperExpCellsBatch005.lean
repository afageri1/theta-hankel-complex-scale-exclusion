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
theorem hpThetaDensityUpperExpCompact_cell100 :
    ∀ t ∈ Set.Icc ((547 / 2000) : ℝ) (549 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((34561221 / 20000000) : ℝ) ≤ Real.exp (2 * (547 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (547 / 2000)) (34561221 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((549 / 2000) : ℝ)) ≤ (216440079 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (549 / 2000)) (216440079 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1182512880229 / 100000) : ℝ) ≤ Real.exp (3 * (5428703 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5428703 / 1000000)) (1182512880229 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((547 / 2000) : ℝ) (549 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5428703 / 1000000) (2719873 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (547 / 2000) (549 / 2000) (34561221 / 20000000) (216440079 / 125000000) (5428703 / 1000000) (2719873 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (547 / 2000) (549 / 2000) (5428703 / 1000000) (2719873 / 500000) (21311 / 250) (10724 / 125)
    (473611 / 1000) (97041 / 200) (770103 / 1000) (3499 / 500000) (7004941 / 500) (21649 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5428703 / 1000000) (1182512880229 / 100000) (21649 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5428703 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5428703 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell101 :
    ∀ t ∈ Set.Icc ((549 / 2000) : ℝ) (551 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1731520631 / 1000000000) : ℝ) ≤ Real.exp (2 * (549 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (549 / 2000)) (1731520631 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((551 / 2000) : ℝ)) ≤ (867493569 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (551 / 2000)) (867493569 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6108456411759 / 500000) : ℝ) ≤ Real.exp (3 * (1359893 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1359893 / 250000)) (6108456411759 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((549 / 2000) : ℝ) (551 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1359893 / 250000) (1362659 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (549 / 2000) (551 / 2000) (1731520631 / 1000000000) (867493569 / 500000000) (1359893 / 250000) (1362659 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (549 / 2000) (551 / 2000) (1359893 / 250000) (1362659 / 250000) (85651 / 1000) (86201 / 1000)
    (11948 / 25) (244787 / 500) (396973 / 500) (3407 / 500000) (14122407 / 1000) (4191 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1359893 / 250000) (6108456411759 / 500000) (4191 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1359893 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1359893 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell102 :
    ∀ t ∈ Set.Icc ((551 / 2000) : ℝ) (553 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1734987137 / 1000000000) : ℝ) ≤ Real.exp (2 * (551 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (551 / 2000)) (1734987137 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((553 / 2000) : ℝ)) ≤ (347692117 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (553 / 2000)) (347692117 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((12622467387109 / 1000000) : ℝ) ≤ Real.exp (3 * (2725231 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2725231 / 500000)) (12622467387109 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((551 / 2000) : ℝ) (553 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2725231 / 500000) (1365387 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (551 / 2000) (553 / 2000) (1734987137 / 1000000000) (347692117 / 200000000) (2725231 / 500000) (1365387 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (551 / 2000) (553 / 2000) (2725231 / 500000) (1365387 / 250000) (4303 / 50) (21653 / 250)
    (24113 / 50) (61747 / 125) (818131 / 1000) (1327 / 200000) (14235837 / 1000) (10141 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2725231 / 500000) (12622467387109 / 1000000) (10141 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2725231 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2725231 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell103 :
    ∀ t ∈ Set.Icc ((553 / 2000) : ℝ) (111 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((217307573 / 125000000) : ℝ) ≤ Real.exp (2 * (553 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (553 / 2000)) (217307573 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((111 / 400) : ℝ)) ≤ (348388197 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (111 / 400)) (348388197 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1304230108997 / 100000) : ℝ) ≤ Real.exp (3 * (5461373 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5461373 / 1000000)) (1304230108997 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((553 / 2000) : ℝ) (111 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5461373 / 1000000) (2736241 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (553 / 2000) (111 / 400) (217307573 / 125000000) (348388197 / 200000000) (5461373 / 1000000) (2736241 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (553 / 2000) (111 / 400) (5461373 / 1000000) (2736241 / 500000) (86471 / 1000) (10878 / 125)
    (60829 / 125) (124603 / 250) (842663 / 1000) (323 / 50000) (14350181 / 1000) (19629 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5461373 / 1000000) (1304230108997 / 100000) (19629 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5461373 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5461373 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell104 :
    ∀ t ∈ Set.Icc ((111 / 400) : ℝ) (557 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((217742623 / 125000000) : ℝ) ≤ Real.exp (2 * (111 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (111 / 400)) (217742623 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((557 / 2000) : ℝ)) ≤ (1745428353 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (557 / 2000)) (1745428353 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((53908091853 / 4000) : ℝ) ≤ Real.exp (3 * (5472307 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5472307 / 1000000)) (53908091853 / 4000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((111 / 400) : ℝ) (557 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5472307 / 1000000) (2741719 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (111 / 400) (557 / 2000) (217742623 / 125000000) (1745428353 / 1000000000) (5472307 / 1000000) (2741719 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (111 / 400) (557 / 2000) (5472307 / 1000000) (2741719 / 500000) (86883 / 1000) (87439 / 1000)
    (491037 / 1000) (12572 / 25) (216881 / 250) (629 / 100000) (14465443 / 1000) (4749 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5472307 / 1000000) (53908091853 / 4000) (4749 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5472307 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5472307 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell105 :
    ∀ t ∈ Set.Icc ((557 / 2000) : ℝ) (559 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((13636159 / 7812500) : ℝ) ≤ Real.exp (2 * (557 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (557 / 2000)) (13636159 / 7812500) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((559 / 2000) : ℝ)) ≤ (1748922703 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (559 / 2000)) (1748922703 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13927147933999 / 1000000) : ℝ) ≤ Real.exp (3 * (5483263 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5483263 / 1000000)) (13927147933999 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((557 / 2000) : ℝ) (559 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5483263 / 1000000) (343401 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (557 / 2000) (559 / 2000) (13636159 / 7812500) (1748922703 / 1000000000) (5483263 / 1000000) (343401 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (557 / 2000) (559 / 2000) (5483263 / 1000000) (343401 / 62500) (43649 / 500) (17571 / 200)
    (123869 / 250) (253691 / 500) (111591 / 125) (6123 / 1000000) (14581633 / 1000) (9191 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5483263 / 1000000) (13927147933999 / 1000000) (9191 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5483263 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5483263 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell106 :
    ∀ t ∈ Set.Icc ((559 / 2000) : ℝ) (561 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((874461351 / 500000000) : ℝ) ≤ Real.exp (2 * (559 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (559 / 2000)) (874461351 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((561 / 2000) : ℝ)) ≤ (1752424049 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (561 / 2000)) (1752424049 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3598301780933 / 250000) : ℝ) ≤ Real.exp (3 * (34339 / 6250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (34339 / 6250)) (3598301780933 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((559 / 2000) : ℝ) (561 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (34339 / 6250) (688177 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (559 / 2000) (561 / 2000) (874461351 / 500000000) (1752424049 / 1000000000) (34339 / 6250) (688177 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (559 / 2000) (561 / 2000) (34339 / 6250) (688177 / 125000) (43857 / 500) (88273 / 1000)
    (124987 / 250) (511917 / 1000) (91829 / 100) (149 / 25000) (2939751 / 200) (17787 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (34339 / 6250) (3598301780933 / 250000) (17787 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (34339 / 6250)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (34339 / 6250)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell107 :
    ∀ t ∈ Set.Icc ((561 / 2000) : ℝ) (563 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((109526503 / 62500000) : ℝ) ≤ Real.exp (2 * (561 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (561 / 2000)) (109526503 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((563 / 2000) : ℝ)) ≤ (438983101 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (563 / 2000)) (438983101 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((7437941029807 / 500000) : ℝ) ≤ Real.exp (3 * (137631 / 25000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (137631 / 25000)) (7437941029807 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((561 / 2000) : ℝ) (563 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (137631 / 25000) (2758219 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (561 / 2000) (563 / 2000) (109526503 / 62500000) (438983101 / 250000000) (137631 / 25000) (2758219 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (561 / 2000) (563 / 2000) (137631 / 25000) (2758219 / 500000) (22033 / 250) (88693 / 1000)
    (504453 / 1000) (516487 / 1000) (118024 / 125) (2901 / 500000) (14816819 / 1000) (1721 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (137631 / 25000) (7437941029807 / 500000) (1721 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (137631 / 25000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (137631 / 25000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell108 :
    ∀ t ∈ Set.Icc ((563 / 2000) : ℝ) (113 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1755932403 / 1000000000) : ℝ) ≤ Real.exp (2 * (563 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (563 / 2000)) (1755932403 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((113 / 400) : ℝ)) ≤ (1759447783 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (113 / 400)) (1759447783 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1537570480277 / 100000) : ℝ) ≤ Real.exp (3 * (5516261 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5516261 / 1000000)) (1537570480277 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((563 / 2000) : ℝ) (113 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5516261 / 1000000) (2763741 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (563 / 2000) (113 / 400) (1755932403 / 1000000000) (1759447783 / 1000000000) (5516261 / 1000000) (2763741 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (563 / 2000) (113 / 400) (5516261 / 1000000) (2763741 / 500000) (88551 / 1000) (17823 / 200)
    (63624 / 125) (52109 / 100) (485229 / 500) (5647 / 1000000) (14935829 / 1000) (333 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5516261 / 1000000) (1537570480277 / 100000) (333 / 20000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5516261 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5516261 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell109 :
    ∀ t ∈ Set.Icc ((113 / 400) : ℝ) (567 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((879723891 / 500000000) : ℝ) ≤ Real.exp (2 * (113 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (113 / 400)) (879723891 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((567 / 2000) : ℝ)) ≤ (8814851 / 5000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (567 / 2000)) (8814851 / 5000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1986676270271 / 125000) : ℝ) ≤ Real.exp (3 * (1105461 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1105461 / 200000)) (1986676270271 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((113 / 400) : ℝ) (567 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1105461 / 200000) (1384637 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (113 / 400) (567 / 2000) (879723891 / 500000000) (8814851 / 5000000) (1105461 / 200000) (1384637 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (113 / 400) (567 / 2000) (1105461 / 200000) (1384637 / 250000) (88973 / 1000) (89539 / 1000)
    (256783 / 500) (65716 / 125) (997073 / 1000) (687 / 125000) (3011159 / 200) (4027 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1105461 / 200000) (1986676270271 / 125000) (4027 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1105461 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1105461 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell110 :
    ∀ t ∈ Set.Icc ((567 / 2000) : ℝ) (569 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1762970199 / 1000000000) : ℝ) ≤ Real.exp (2 * (567 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (567 / 2000)) (1762970199 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((569 / 2000) : ℝ)) ≤ (1766499669 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (569 / 2000)) (1766499669 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3285914723999 / 200000) : ℝ) ≤ Real.exp (3 * (553837 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (553837 / 100000)) (3285914723999 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((567 / 2000) : ℝ) (569 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (553837 / 100000) (1387409 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (567 / 2000) (569 / 2000) (1762970199 / 1000000000) (1766499669 / 1000000000) (553837 / 100000) (1387409 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (567 / 2000) (569 / 2000) (553837 / 100000) (1387409 / 250000) (22349 / 250) (22491 / 250)
    (518173 / 1000) (530401 / 1000) (51203 / 50) (1337 / 250000) (7588361 / 500) (7791 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (553837 / 100000) (3285914723999 / 200000) (7791 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (553837 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (553837 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell111 :
    ∀ t ∈ Set.Icc ((569 / 2000) : ℝ) (571 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((441624917 / 250000000) : ℝ) ≤ Real.exp (2 * (569 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (569 / 2000)) (441624917 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((571 / 2000) : ℝ)) ≤ (1770036203 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (571 / 2000)) (1770036203 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4246246905217 / 250000) : ℝ) ≤ Real.exp (3 * (2774729 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2774729 / 500000)) (4246246905217 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((569 / 2000) : ℝ) (571 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2774729 / 500000) (2780373 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (569 / 2000) (571 / 2000) (441624917 / 250000000) (1770036203 / 1000000000) (2774729 / 500000) (2780373 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (569 / 2000) (571 / 2000) (2774729 / 500000) (2780373 / 500000) (89821 / 1000) (90391 / 1000)
    (104563 / 200) (133777 / 250) (525701 / 500) (1041 / 200000) (15298619 / 1000) (15073 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2774729 / 500000) (4246246905217 / 250000) (15073 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2774729 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2774729 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell112 :
    ∀ t ∈ Set.Icc ((571 / 2000) : ℝ) (573 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((885018101 / 500000000) : ℝ) ≤ Real.exp (2 * (571 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (571 / 2000)) (885018101 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((573 / 2000) : ℝ)) ≤ (886789909 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (573 / 2000)) (886789909 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((17560327383983 / 1000000) : ℝ) ≤ Real.exp (3 * (695071 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (695071 / 125000)) (17560327383983 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((571 / 2000) : ℝ) (573 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (695071 / 125000) (5571879 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (571 / 2000) (573 / 2000) (885018101 / 500000000) (886789909 / 500000000) (695071 / 125000) (5571879 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (571 / 2000) (573 / 2000) (695071 / 125000) (5571879 / 1000000) (11281 / 125) (4541 / 50)
    (527491 / 1000) (10797 / 20) (1079127 / 1000) (1013 / 200000) (15421503 / 1000) (14579 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (695071 / 125000) (17560327383983 / 1000000) (14579 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (695071 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (695071 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell113 :
    ∀ t ∈ Set.Icc ((573 / 2000) : ℝ) (23 / 80), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1773579817 / 1000000000) : ℝ) ≤ Real.exp (2 * (573 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (573 / 2000)) (1773579817 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((23 / 80) : ℝ)) ≤ (1777130527 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (23 / 80)) (1777130527 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((9078172097017 / 500000) : ℝ) ≤ Real.exp (3 * (55717 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (55717 / 10000)) (9078172097017 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((573 / 2000) : ℝ) (23 / 80),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (55717 / 10000) (2791517 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (573 / 2000) (23 / 80) (1773579817 / 1000000000) (1777130527 / 1000000000) (55717 / 10000) (2791517 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (573 / 2000) (23 / 80) (55717 / 10000) (2791517 / 500000) (90677 / 1000) (91251 / 1000)
    (532203 / 1000) (136157 / 250) (553613 / 500) (77 / 15625) (15545371 / 1000) (141 / 10000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (55717 / 10000) (9078172097017 / 500000) (141 / 10000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (55717 / 10000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (55717 / 10000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell114 :
    ∀ t ∈ Set.Icc ((23 / 80) : ℝ) (577 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((888565263 / 500000000) : ℝ) ≤ Real.exp (2 * (23 / 80)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (23 / 80)) (888565263 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((577 / 2000) : ℝ)) ≤ (356137669 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (577 / 2000)) (356137669 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3754775038691 / 200000) : ℝ) ≤ Real.exp (3 * (1116571 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1116571 / 200000)) (3754775038691 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((23 / 80) : ℝ) (577 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1116571 / 200000) (5594211 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (23 / 80) (577 / 2000) (888565263 / 500000000) (356137669 / 200000000) (1116571 / 200000) (5594211 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (23 / 80) (577 / 2000) (1116571 / 200000) (5594211 / 1000000) (91107 / 1000) (22921 / 250)
    (10739 / 20) (549441 / 1000) (283923 / 250) (2397 / 500000) (1567023 / 100) (3409 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1116571 / 200000) (3754775038691 / 200000) (3409 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1116571 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1116571 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell115 :
    ∀ t ∈ Set.Icc ((577 / 2000) : ℝ) (579 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((222586043 / 125000000) : ℝ) ≤ Real.exp (2 * (577 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (577 / 2000)) (222586043 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((579 / 2000) : ℝ)) ≤ (892126643 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (579 / 2000)) (892126643 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((9706839778361 / 500000) : ℝ) ≤ Real.exp (3 * (349627 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (349627 / 62500)) (9706839778361 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((577 / 2000) : ℝ) (579 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (349627 / 62500) (5605411 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (577 / 2000) (579 / 2000) (222586043 / 125000000) (892126643 / 500000000) (349627 / 62500) (5605411 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (577 / 2000) (579 / 2000) (349627 / 62500) (5605411 / 1000000) (4577 / 50) (92119 / 1000)
    (135433 / 250) (55429 / 100) (1164553 / 1000) (583 / 125000) (15796099 / 1000) (13187 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (349627 / 62500) (9706839778361 / 500000) (13187 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (349627 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (349627 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell116 :
    ∀ t ∈ Set.Icc ((579 / 2000) : ℝ) (581 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((356850657 / 200000000) : ℝ) ≤ Real.exp (2 * (579 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (579 / 2000)) (356850657 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((581 / 2000) : ℝ)) ≤ (1787825363 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (581 / 2000)) (1787825363 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((627393786151 / 31250) : ℝ) ≤ Real.exp (3 * (5605231 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5605231 / 1000000)) (627393786151 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((579 / 2000) : ℝ) (581 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5605231 / 1000000) (5616633 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (579 / 2000) (581 / 2000) (356850657 / 200000000) (1787825363 / 1000000000) (5605231 / 1000000) (5616633 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (579 / 2000) (581 / 2000) (5605231 / 1000000) (5616633 / 1000000) (45987 / 500) (18511 / 200)
    (10931 / 20) (22367 / 40) (1193799 / 1000) (2269 / 500000) (7961487 / 500) (797 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5605231 / 1000000) (627393786151 / 31250) (797 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5605231 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5605231 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell117 :
    ∀ t ∈ Set.Icc ((581 / 2000) : ℝ) (583 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((893912681 / 500000000) : ℝ) ≤ Real.exp (2 * (581 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (581 / 2000)) (893912681 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((583 / 2000) : ℝ)) ≤ (111962787 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (583 / 2000)) (111962787 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((5190894869473 / 250000) : ℝ) ≤ Real.exp (3 * (5616453 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5616453 / 1000000)) (5190894869473 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((581 / 2000) : ℝ) (583 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5616453 / 1000000) (5627877 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (581 / 2000) (583 / 2000) (893912681 / 500000000) (111962787 / 62500000) (5616453 / 1000000) (5627877 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (581 / 2000) (583 / 2000) (5616453 / 1000000) (5627877 / 1000000) (9241 / 100) (46497 / 500)
    (137851 / 250) (70512 / 125) (152928 / 125) (2207 / 500000) (16050863 / 1000) (1233 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5616453 / 1000000) (5190894869473 / 250000) (1233 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5616453 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5616453 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell118 :
    ∀ t ∈ Set.Icc ((583 / 2000) : ℝ) (117 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1791404591 / 1000000000) : ℝ) ≤ Real.exp (2 * (583 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (583 / 2000)) (1791404591 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((117 / 400) : ℝ)) ≤ (897495493 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (117 / 400)) (897495493 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((10737734246911 / 500000) : ℝ) ≤ Real.exp (3 * (5627697 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5627697 / 1000000)) (10737734246911 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((583 / 2000) : ℝ) (117 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5627697 / 1000000) (704893 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (583 / 2000) (117 / 400) (1791404591 / 1000000000) (897495493 / 500000000) (5627697 / 1000000) (704893 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (583 / 2000) (117 / 400) (5627697 / 1000000) (704893 / 125000) (92849 / 1000) (46717 / 500)
    (278147 / 500) (284527 / 500) (1253457 / 1000) (4293 / 1000000) (3235957 / 200) (11921 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5627697 / 1000000) (10737734246911 / 500000) (11921 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5627697 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5627697 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell119 :
    ∀ t ∈ Set.Icc ((117 / 400) : ℝ) (587 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((358998197 / 200000000) : ℝ) ≤ Real.exp (2 * (117 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (117 / 400)) (358998197 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((587 / 2000) : ℝ)) ≤ (22482307 / 12500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (587 / 2000)) (22482307 / 12500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4442656629461 / 200000) : ℝ) ≤ Real.exp (3 * (1409741 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1409741 / 250000)) (4442656629461 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((117 / 400) : ℝ) (587 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1409741 / 250000) (2825217 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (117 / 400) (587 / 2000) (358998197 / 200000000) (22482307 / 12500000) (1409741 / 250000) (2825217 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (117 / 400) (587 / 2000) (1409741 / 250000) (2825217 / 500000) (93289 / 1000) (23469 / 250)
    (28061 / 50) (574049 / 1000) (128389 / 100) (167 / 40000) (16309747 / 1000) (461 / 40000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1409741 / 250000) (4442656629461 / 200000) (461 / 40000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1409741 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1409741 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityUpperExpCompact_cellsBatch005 :
    ∀ t ∈ Set.Icc ((547 / 2000) : ℝ) (587 / 2000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell100
      hpThetaDensityUpperExpCompact_cell101)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell102
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell103
      hpThetaDensityUpperExpCompact_cell104)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell105
      hpThetaDensityUpperExpCompact_cell106)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell107
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell108
      hpThetaDensityUpperExpCompact_cell109))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell110
      hpThetaDensityUpperExpCompact_cell111)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell112
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell113
      hpThetaDensityUpperExpCompact_cell114)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell115
      hpThetaDensityUpperExpCompact_cell116)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell117
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell118
      hpThetaDensityUpperExpCompact_cell119)))))

#print axioms hpThetaDensityUpperExpCompact_cellsBatch005
end HodgeProofHP
