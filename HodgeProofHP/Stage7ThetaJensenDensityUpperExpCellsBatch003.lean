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
theorem hpThetaDensityUpperExpCompact_cell060 :
    ∀ t ∈ Set.Icc ((467 / 2000) : ℝ) (469 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1595201403 / 1000000000) : ℝ) ≤ Real.exp (2 * (467 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (467 / 2000)) (1595201403 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((469 / 2000) : ℝ)) ≤ (1598394999 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (469 / 2000)) (1598394999 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((338167254889 / 100000) : ℝ) ≤ Real.exp (3 * (200453 / 40000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (200453 / 40000)) (338167254889 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((467 / 2000) : ℝ) (469 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (200453 / 40000) (2510759 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (467 / 2000) (469 / 2000) (1595201403 / 1000000000) (1598394999 / 1000000000) (200453 / 40000) (2510759 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (467 / 2000) (469 / 2000) (200453 / 40000) (2510759 / 500000) (17581 / 250) (14159 / 200)
    (32551 / 100) (41861 / 125) (5057 / 100) (1203 / 62500) (10173259 / 1000) (75703 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (200453 / 40000) (338167254889 / 100000) (75703 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (200453 / 40000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (200453 / 40000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell061 :
    ∀ t ∈ Set.Icc ((469 / 2000) : ℝ) (471 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((799197499 / 500000000) : ℝ) ≤ Real.exp (2 * (469 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (469 / 2000)) (799197499 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((471 / 2000) : ℝ)) ≤ (400398747 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (471 / 2000)) (400398747 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3484982528891 / 1000000) : ℝ) ≤ Real.exp (3 * (5021357 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5021357 / 1000000)) (3484982528891 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((469 / 2000) : ℝ) (471 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5021357 / 1000000) (5031571 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (469 / 2000) (471 / 2000) (799197499 / 500000000) (400398747 / 250000000) (5021357 / 1000000) (5031571 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (469 / 2000) (471 / 2000) (5021357 / 1000000) (5031571 / 1000000) (35333 / 500) (71139 / 1000)
    (41086 / 125) (84529 / 250) (1594 / 25) (1879 / 100000) (10254971 / 1000) (73459 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5021357 / 1000000) (3484982528891 / 1000000) (73459 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5021357 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5021357 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell062 :
    ∀ t ∈ Set.Icc ((471 / 2000) : ℝ) (473 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1601594987 / 1000000000) : ℝ) ≤ Real.exp (2 * (471 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (471 / 2000)) (1601594987 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((473 / 2000) : ℝ)) ≤ (1604801383 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (473 / 2000)) (1604801383 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((143666978903 / 40000) : ℝ) ≤ Real.exp (3 * (503141 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (503141 / 100000)) (143666978903 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((471 / 2000) : ℝ) (473 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (503141 / 100000) (1008329 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (471 / 2000) (473 / 2000) (1601594987 / 1000000000) (1604801383 / 1000000000) (503141 / 100000) (1008329 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (471 / 2000) (473 / 2000) (503141 / 100000) (1008329 / 200000) (7101 / 100) (14297 / 200)
    (33189 / 100) (42671 / 125) (19291 / 250) (9171 / 500000) (5168673 / 500) (17819 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (503141 / 100000) (143666978903 / 40000) (17819 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (503141 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (503141 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell063 :
    ∀ t ∈ Set.Icc ((473 / 2000) : ℝ) (19 / 80), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((802400691 / 500000000) : ℝ) ≤ Real.exp (2 * (473 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (473 / 2000)) (802400691 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((19 / 80) : ℝ)) ≤ (804007099 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (19 / 80)) (804007099 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1850927211797 / 500000) : ℝ) ≤ Real.exp (3 * (5041483 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5041483 / 1000000)) (1850927211797 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((473 / 2000) : ℝ) (19 / 80),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5041483 / 1000000) (2525869 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (473 / 2000) (19 / 80) (802400691 / 500000000) (804007099 / 500000000) (5041483 / 1000000) (2525869 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (473 / 2000) (19 / 80) (5041483 / 1000000) (2525869 / 500000) (14271 / 200) (8979 / 125)
    (335117 / 1000) (68929 / 200) (90771 / 1000) (17903 / 1000000) (10420373 / 1000) (13831 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5041483 / 1000000) (1850927211797 / 500000) (13831 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5041483 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5041483 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell064 :
    ∀ t ∈ Set.Icc ((19 / 80) : ℝ) (477 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1608014197 / 1000000000) : ℝ) ≤ Real.exp (2 * (19 / 80)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (19 / 80)) (1608014197 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((477 / 2000) : ℝ)) ≤ (322246689 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (477 / 2000)) (322246689 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((23847767279 / 6250) : ℝ) ≤ Real.exp (3 * (631447 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (631447 / 125000)) (23847767279 / 6250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((19 / 80) : ℝ) (477 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (631447 / 125000) (5061851 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (19 / 80) (477 / 2000) (1608014197 / 1000000000) (322246689 / 200000000) (631447 / 125000) (5061851 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (19 / 80) (477 / 2000) (631447 / 125000) (5061851 / 1000000) (35851 / 500) (3609 / 50)
    (338369 / 1000) (347947 / 1000) (52297 / 500) (8737 / 500000) (5252033 / 500) (67093 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (631447 / 125000) (23847767279 / 6250) (67093 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (631447 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (631447 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell065 :
    ∀ t ∈ Set.Icc ((477 / 2000) : ℝ) (479 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((402808361 / 250000000) : ℝ) ≤ Real.exp (2 * (477 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (477 / 2000)) (402808361 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((479 / 2000) : ℝ)) ≤ (6306481 / 3906250) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (479 / 2000)) (6306481 / 3906250) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3933164231387 / 1000000) : ℝ) ≤ Real.exp (3 * (5061689 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5061689 / 1000000)) (3933164231387 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((477 / 2000) : ℝ) (479 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5061689 / 1000000) (1014397 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (477 / 2000) (479 / 2000) (402808361 / 250000000) (6306481 / 3906250) (5061689 / 1000000) (1014397 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (477 / 2000) (479 / 2000) (5061689 / 1000000) (1014397 / 200000) (1441 / 20) (7253 / 100)
    (170823 / 500) (14051 / 40) (59323 / 500) (17053 / 1000000) (10588437 / 1000) (1017 / 15625000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5061689 / 1000000) (3933164231387 / 1000000) (1017 / 15625000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5061689 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5061689 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell066 :
    ∀ t ∈ Set.Icc ((479 / 2000) : ℝ) (481 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((322891827 / 200000000) : ℝ) ≤ Real.exp (2 * (479 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (479 / 2000)) (322891827 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((481 / 2000) : ℝ)) ≤ (323538257 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (481 / 2000)) (323538257 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4054560238503 / 1000000) : ℝ) ≤ Real.exp (3 * (5071823 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5071823 / 1000000)) (4054560238503 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((479 / 2000) : ℝ) (481 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5071823 / 1000000) (5082139 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (479 / 2000) (481 / 2000) (322891827 / 200000000) (323538257 / 200000000) (5071823 / 1000000) (5082139 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (479 / 2000) (481 / 2000) (5071823 / 1000000) (5082139 / 1000000) (362 / 5) (36441 / 500)
    (344949 / 1000) (88657 / 250) (132911 / 1000) (8321 / 500000) (10673483 / 1000) (63139 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5071823 / 1000000) (4054560238503 / 1000000) (63139 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5071823 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5071823 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell067 :
    ∀ t ∈ Set.Icc ((481 / 2000) : ℝ) (483 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((404422821 / 250000000) : ℝ) ≤ Real.exp (2 * (481 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (481 / 2000)) (404422821 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((483 / 2000) : ℝ)) ≤ (810464953 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (483 / 2000)) (810464953 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((522494164507 / 125000) : ℝ) ≤ Real.exp (3 * (5081977 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5081977 / 1000000)) (522494164507 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((481 / 2000) : ℝ) (483 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5081977 / 1000000) (2546157 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (481 / 2000) (483 / 2000) (404422821 / 250000000) (810464953 / 500000000) (5081977 / 1000000) (2546157 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (481 / 2000) (483 / 2000) (5081977 / 1000000) (2546157 / 500000) (9094 / 125) (14647 / 200)
    (87069 / 250) (44751 / 125) (147409 / 1000) (203 / 12500) (5379609 / 500) (12249 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5081977 / 1000000) (522494164507 / 125000) (12249 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5081977 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5081977 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell068 :
    ∀ t ∈ Set.Icc ((483 / 2000) : ℝ) (97 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((324185981 / 200000000) : ℝ) ≤ Real.exp (2 * (483 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (483 / 2000)) (324185981 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((97 / 400) : ℝ)) ≤ (1624175009 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (97 / 400)) (1624175009 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2154741152819 / 500000) : ℝ) ≤ Real.exp (3 * (5092151 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5092151 / 1000000)) (2154741152819 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((483 / 2000) : ℝ) (97 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5092151 / 1000000) (5102509 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (483 / 2000) (97 / 400) (324185981 / 200000000) (1624175009 / 1000000000) (5092151 / 1000000) (5102509 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (483 / 2000) (97 / 400) (5092151 / 1000000) (5102509 / 1000000) (9138 / 125) (7359 / 100)
    (35163 / 100) (361413 / 1000) (81067 / 500) (15847 / 1000000) (5422819 / 500) (14851 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5092151 / 1000000) (2154741152819 / 500000) (14851 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5092151 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5092151 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell069 :
    ∀ t ∈ Set.Icc ((97 / 400) : ℝ) (487 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((50755469 / 31250000) : ℝ) ≤ Real.exp (2 * (97 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (97 / 400)) (50755469 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((487 / 2000) : ℝ)) ≤ (162742661 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (487 / 2000)) (162742661 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4443291098953 / 1000000) : ℝ) ≤ Real.exp (3 * (1020469 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1020469 / 200000)) (4443291098953 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((97 / 400) : ℝ) (487 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1020469 / 200000) (1278181 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (97 / 400) (487 / 2000) (50755469 / 31250000) (162742661 / 100000000) (1020469 / 200000) (1278181 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (97 / 400) (487 / 2000) (1020469 / 200000) (1278181 / 250000) (73459 / 1000) (36973 / 500)
    (355009 / 1000) (91211 / 250) (22136 / 125) (7731 / 500000) (43731 / 4) (11523 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1020469 / 200000) (4443291098953 / 1000000) (11523 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1020469 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1020469 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell070 :
    ∀ t ∈ Set.Icc ((487 / 2000) : ℝ) (489 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1627426609 / 1000000000) : ℝ) ≤ Real.exp (2 * (487 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (487 / 2000)) (1627426609 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((489 / 2000) : ℝ)) ≤ (20383559 / 12500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (489 / 2000)) (20383559 / 12500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2290771285809 / 500000) : ℝ) ≤ Real.exp (3 * (63907 / 12500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (63907 / 12500)) (2290771285809 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((487 / 2000) : ℝ) (489 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (63907 / 12500) (64037 / 12500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (487 / 2000) (489 / 2000) (1627426609 / 1000000000) (20383559 / 12500000) (63907 / 12500) (64037 / 12500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (487 / 2000) (489 / 2000) (63907 / 12500) (64037 / 12500) (14763 / 200) (9288 / 125)
    (179207 / 500) (184151 / 500) (96137 / 500) (7543 / 500000) (2204113 / 200) (55877 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (63907 / 12500) (2290771285809 / 500000) (55877 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (63907 / 12500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (63907 / 12500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell071 :
    ∀ t ∈ Set.Icc ((489 / 2000) : ℝ) (491 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1630684719 / 1000000000) : ℝ) ≤ Real.exp (2 * (489 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (489 / 2000)) (1630684719 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((491 / 2000) : ℝ)) ≤ (1633949353 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (491 / 2000)) (1633949353 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((118109814551 / 25000) : ℝ) ≤ Real.exp (3 * (1280699 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1280699 / 250000)) (118109814551 / 25000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((489 / 2000) : ℝ) (491 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1280699 / 250000) (160413 / 31250) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (489 / 2000) (491 / 2000) (1630684719 / 1000000000) (1633949353 / 1000000000) (1280699 / 250000) (160413 / 31250) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (489 / 2000) (491 / 2000) (1280699 / 250000) (160413 / 31250) (18543 / 250) (74663 / 1000)
    (180923 / 500) (185893 / 500) (41537 / 200) (7359 / 500000) (5554541 / 500) (54187 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1280699 / 250000) (118109814551 / 25000) (54187 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1280699 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1280699 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell072 :
    ∀ t ∈ Set.Icc ((491 / 2000) : ℝ) (493 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((204243669 / 125000000) : ℝ) ≤ Real.exp (2 * (491 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (491 / 2000)) (204243669 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((493 / 2000) : ℝ)) ≤ (818610261 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (493 / 2000)) (818610261 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4871973493713 / 1000000) : ℝ) ≤ Real.exp (3 * (5133051 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5133051 / 1000000)) (4871973493713 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((491 / 2000) : ℝ) (493 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5133051 / 1000000) (1285873 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (491 / 2000) (493 / 2000) (204243669 / 125000000) (818610261 / 500000000) (5133051 / 1000000) (1285873 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (491 / 2000) (493 / 2000) (5133051 / 1000000) (1285873 / 250000) (74531 / 1000) (9378 / 125)
    (45663 / 125) (46912 / 125) (111671 / 500) (7179 / 500000) (2239661 / 200) (26273 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5133051 / 1000000) (4871973493713 / 1000000) (26273 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5133051 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5133051 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell073 :
    ∀ t ∈ Set.Icc ((493 / 2000) : ℝ) (99 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1637220521 / 1000000000) : ℝ) ≤ Real.exp (2 * (493 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (493 / 2000)) (1637220521 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((99 / 400) : ℝ)) ≤ (5126557 / 3125000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (99 / 400)) (5126557 / 3125000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((628061914727 / 125000) : ℝ) ≤ Real.exp (3 * (160729 / 31250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (160729 / 31250)) (628061914727 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((493 / 2000) : ℝ) (99 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (160729 / 31250) (515379 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (493 / 2000) (99 / 400) (1637220521 / 1000000000) (5126557 / 3125000) (160729 / 31250) (515379 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (493 / 2000) (99 / 400) (160729 / 31250) (515379 / 100000) (18723 / 250) (75387 / 1000)
    (92197 / 250) (189417 / 500) (239241 / 1000) (7003 / 500000) (11288257 / 1000) (50951 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (160729 / 31250) (628061914727 / 125000) (50951 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (160729 / 31250)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (160729 / 31250)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell074 :
    ∀ t ∈ Set.Icc ((99 / 400) : ℝ) (497 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1640498239 / 1000000000) : ℝ) ≤ Real.exp (2 * (99 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (99 / 400)) (1640498239 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((497 / 2000) : ℝ)) ≤ (1643782519 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (497 / 2000)) (1643782519 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((5182102016573 / 1000000) : ℝ) ≤ Real.exp (3 * (41229 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (41229 / 8000)) (5182102016573 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((99 / 400) : ℝ) (497 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (41229 / 8000) (1291027 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (99 / 400) (497 / 2000) (1640498239 / 1000000000) (1643782519 / 1000000000) (41229 / 8000) (1291027 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (99 / 400) (497 / 2000) (41229 / 8000) (1291027 / 250000) (37627 / 500) (75751 / 1000)
    (3723 / 10) (382399 / 1000) (127691 / 500) (6831 / 500000) (5689463 / 500) (49401 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (41229 / 8000) (5182102016573 / 1000000) (49401 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (41229 / 8000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (41229 / 8000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell075 :
    ∀ t ∈ Set.Icc ((497 / 2000) : ℝ) (499 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((821891259 / 500000000) : ℝ) ≤ Real.exp (2 * (497 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (497 / 2000)) (821891259 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((499 / 2000) : ℝ)) ≤ (823536687 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (499 / 2000)) (823536687 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2672486108609 / 500000) : ℝ) ≤ Real.exp (3 * (2581971 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2581971 / 500000)) (2672486108609 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((497 / 2000) : ℝ) (499 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2581971 / 500000) (2587223 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (497 / 2000) (499 / 2000) (821891259 / 500000000) (823536687 / 500000000) (2581971 / 500000) (2587223 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (497 / 2000) (499 / 2000) (2581971 / 500000) (2587223 / 500000) (37809 / 500) (19029 / 250)
    (187919 / 500) (38599 / 100) (271767 / 1000) (533 / 40000) (11470317 / 1000) (5987 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2581971 / 500000) (2672486108609 / 500000) (5987 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2581971 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2581971 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell076 :
    ∀ t ∈ Set.Icc ((499 / 2000) : ℝ) (501 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1647073373 / 1000000000) : ℝ) ≤ Real.exp (2 * (499 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (499 / 2000)) (1647073373 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((501 / 2000) : ℝ)) ≤ (1650370817 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (501 / 2000)) (1650370817 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((551332418543 / 100000) : ℝ) ≤ Real.exp (3 * (5174281 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5174281 / 1000000)) (551332418543 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((499 / 2000) : ℝ) (501 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5174281 / 1000000) (1036961 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (499 / 2000) (501 / 2000) (1647073373 / 1000000000) (1650370817 / 1000000000) (5174281 / 1000000) (1036961 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (499 / 2000) (501 / 2000) (5174281 / 1000000) (1036961 / 200000) (75983 / 1000) (19121 / 250)
    (379403 / 1000) (389609 / 1000) (36049 / 125) (3249 / 250000) (5781223 / 500) (46433 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5174281 / 1000000) (551332418543 / 100000) (46433 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5174281 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5174281 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell077 :
    ∀ t ∈ Set.Icc ((501 / 2000) : ℝ) (503 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((6446761 / 3906250) : ℝ) ≤ Real.exp (2 * (501 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (501 / 2000)) (6446761 / 3906250) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((503 / 2000) : ℝ)) ≤ (826837431 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (503 / 2000)) (826837431 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2843650941641 / 500000) : ℝ) ≤ Real.exp (3 * (5184639 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5184639 / 1000000)) (2843650941641 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((501 / 2000) : ℝ) (503 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5184639 / 1000000) (1039037 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (501 / 2000) (503 / 2000) (6446761 / 3906250) (826837431 / 500000000) (5184639 / 1000000) (1039037 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (501 / 2000) (503 / 2000) (5184639 / 1000000) (1039037 / 200000) (1527 / 20) (19213 / 250)
    (76599 / 200) (49157 / 125) (305287 / 1000) (6337 / 500000) (2913829 / 250) (45013 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5184639 / 1000000) (2843650941641 / 500000) (45013 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5184639 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5184639 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell078 :
    ∀ t ∈ Set.Icc ((503 / 2000) : ℝ) (101 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1653674861 / 1000000000) : ℝ) ≤ Real.exp (2 * (503 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (503 / 2000)) (1653674861 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((101 / 400) : ℝ)) ≤ (1656985521 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (101 / 400)) (1656985521 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2933577838107 / 500000) : ℝ) ≤ Real.exp (3 * (5195019 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5195019 / 1000000)) (2933577838107 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((503 / 2000) : ℝ) (101 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5195019 / 1000000) (2602793 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (503 / 2000) (101 / 400) (1653674861 / 1000000000) (1656985521 / 1000000000) (5195019 / 1000000) (2602793 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (503 / 2000) (101 / 400) (5195019 / 1000000) (2602793 / 500000) (76719 / 1000) (77223 / 1000)
    (48327 / 125) (396931 / 1000) (80607 / 250) (309 / 25000) (2349787 / 200) (43633 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5195019 / 1000000) (2933577838107 / 500000) (43633 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5195019 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5195019 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell079 :
    ∀ t ∈ Set.Icc ((101 / 400) : ℝ) (507 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((20712319 / 12500000) : ℝ) ≤ Real.exp (2 * (101 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (101 / 400)) (20712319 / 12500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((507 / 2000) : ℝ)) ≤ (207537851 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (507 / 2000)) (207537851 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6053077241443 / 1000000) : ℝ) ≤ Real.exp (3 * (260271 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (260271 / 50000)) (6053077241443 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((101 / 400) : ℝ) (507 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (260271 / 50000) (652001 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (101 / 400) (507 / 2000) (20712319 / 12500000) (207537851 / 125000000) (260271 / 50000) (652001 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (101 / 400) (507 / 2000) (260271 / 50000) (652001 / 125000) (77089 / 1000) (15519 / 200)
    (48783 / 125) (400633 / 1000) (169913 / 500) (3013 / 250000) (11843307 / 1000) (42293 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (260271 / 50000) (6053077241443 / 1000000) (42293 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (260271 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (260271 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityUpperExpCompact_cellsBatch003 :
    ∀ t ∈ Set.Icc ((467 / 2000) : ℝ) (507 / 2000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell060
      hpThetaDensityUpperExpCompact_cell061)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell062
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell063
      hpThetaDensityUpperExpCompact_cell064)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell065
      hpThetaDensityUpperExpCompact_cell066)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell067
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell068
      hpThetaDensityUpperExpCompact_cell069))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell070
      hpThetaDensityUpperExpCompact_cell071)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell072
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell073
      hpThetaDensityUpperExpCompact_cell074)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell075
      hpThetaDensityUpperExpCompact_cell076)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell077
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell078
      hpThetaDensityUpperExpCompact_cell079)))))

#print axioms hpThetaDensityUpperExpCompact_cellsBatch003
end HodgeProofHP
