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
theorem hpThetaDensityUpperExpCompact_cell220 :
    ∀ t ∈ Set.Icc ((787 / 2000) : ℝ) (789 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1098398071 / 500000000) : ℝ) ≤ Real.exp (2 * (787 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (787 / 2000)) (1098398071 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((789 / 2000) : ℝ)) ≤ (550298533 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (789 / 2000)) (550298533 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((968189413042041 / 1000000) : ℝ) ≤ Real.exp (3 * (1380247 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1380247 / 200000)) (968189413042041 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((787 / 2000) : ℝ) (789 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1380247 / 200000) (864409 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (787 / 2000) (789 / 2000) (1098398071 / 500000000) (550298533 / 250000000) (1380247 / 200000) (864409 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (787 / 2000) (789 / 2000) (1380247 / 200000) (864409 / 125000) (18627 / 125) (149877 / 1000)
    (324593 / 250) (1320479 / 1000) (926056 / 125) (11 / 62500) (36589549 / 1000) (53 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1380247 / 200000) (968189413042041 / 1000000) (53 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1380247 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1380247 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell221 :
    ∀ t ∈ Set.Icc ((789 / 2000) : ℝ) (791 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2201194131 / 1000000000) : ℝ) ≤ Real.exp (2 * (789 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (789 / 2000)) (2201194131 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((791 / 2000) : ℝ)) ≤ (88224037 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (791 / 2000)) (88224037 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1008829179585073 / 1000000) : ℝ) ≤ Real.exp (3 * (6915051 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6915051 / 1000000)) (1008829179585073 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((789 / 2000) : ℝ) (791 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6915051 / 1000000) (1732279 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (789 / 2000) (791 / 2000) (2201194131 / 1000000000) (88224037 / 40000000) (6915051 / 1000000) (1732279 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (789 / 2000) (791 / 2000) (6915051 / 1000000) (1732279 / 250000) (149697 / 1000) (150561 / 1000)
    (1308653 / 1000) (1330881 / 1000) (75119 / 10) (17 / 100000) (36883431 / 1000) (127 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6915051 / 1000000) (1008829179585073 / 1000000) (127 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6915051 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6915051 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell222 :
    ∀ t ∈ Set.Icc ((791 / 2000) : ℝ) (793 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((551400231 / 250000000) : ℝ) ≤ Real.exp (2 * (791 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (791 / 2000)) (551400231 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((793 / 2000) : ℝ)) ≤ (2210016541 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (793 / 2000)) (2210016541 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((262813769494979 / 250000) : ℝ) ≤ Real.exp (3 * (1385779 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1385779 / 200000)) (262813769494979 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((791 / 2000) : ℝ) (793 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1385779 / 200000) (1735747 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (791 / 2000) (793 / 2000) (551400231 / 250000000) (2210016541 / 1000000000) (1385779 / 200000) (1735747 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (791 / 2000) (793 / 2000) (1385779 / 200000) (1735747 / 250000) (7519 / 50) (151247 / 1000)
    (1319007 / 1000) (335339 / 250) (3808253 / 500) (41 / 250000) (929492 / 25) (61 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1385779 / 200000) (262813769494979 / 250000) (61 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1385779 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1385779 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell223 :
    ∀ t ∈ Set.Icc ((793 / 2000) : ℝ) (159 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((110500827 / 50000000) : ℝ) ≤ Real.exp (2 * (793 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (793 / 2000)) (110500827 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((159 / 400) : ℝ)) ≤ (2214440997 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (159 / 400)) (2214440997 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1095545416919517 / 1000000) : ℝ) ≤ Real.exp (3 * (3471383 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3471383 / 500000)) (1095545416919517 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((793 / 2000) : ℝ) (159 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3471383 / 500000) (869611 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (793 / 2000) (159 / 400) (110500827 / 50000000) (2214440997 / 1000000000) (3471383 / 500000) (869611 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (793 / 2000) (159 / 400) (3471383 / 500000) (869611 / 125000) (75533 / 500) (151937 / 1000)
    (664717 / 500) (675953 / 500) (3861147 / 500) (159 / 1000000) (37478313 / 1000) (117 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3471383 / 500000) (1095545416919517 / 1000000) (117 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3471383 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3471383 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell224 :
    ∀ t ∈ Set.Icc ((159 / 400) : ℝ) (797 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((553610249 / 250000000) : ℝ) ≤ Real.exp (2 * (159 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (159 / 400)) (553610249 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((797 / 2000) : ℝ)) ≤ (2218874311 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (797 / 2000)) (2218874311 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1141791992638861 / 1000000) : ℝ) ≤ Real.exp (3 * (3478333 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3478333 / 500000)) (1141791992638861 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((159 / 400) : ℝ) (797 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3478333 / 500000) (108919 / 15625) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (159 / 400) (797 / 2000) (553610249 / 250000000) (2218874311 / 1000000000) (3478333 / 500000) (108919 / 15625) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (159 / 400) (797 / 2000) (3478333 / 500000) (108919 / 15625) (30351 / 200) (15263 / 100)
    (267987 / 200) (1362529 / 1000) (7829243 / 1000) (77 / 500000) (37779349 / 1000) (9 / 40000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3478333 / 500000) (1141791992638861 / 1000000) (9 / 40000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3478333 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3478333 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell225 :
    ∀ t ∈ Set.Icc ((797 / 2000) : ℝ) (799 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((221887431 / 100000000) : ℝ) ≤ Real.exp (2 * (797 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (797 / 2000)) (221887431 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((799 / 2000) : ℝ)) ≤ (4446633 / 2000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (799 / 2000)) (4446633 / 2000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1190077586829223 / 1000000) : ℝ) ≤ Real.exp (3 * (6970593 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6970593 / 1000000)) (1190077586829223 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((797 / 2000) : ℝ) (799 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6970593 / 1000000) (1746193 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (797 / 2000) (799 / 2000) (221887431 / 100000000) (4446633 / 2000000) (6970593 / 1000000) (1746193 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (797 / 2000) (799 / 2000) (6970593 / 1000000) (1746193 / 250000) (19056 / 125) (6133 / 40)
    (135051 / 100) (343307 / 250) (1587479 / 200) (37 / 250000) (7616561 / 200) (27 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6970593 / 1000000) (1190077586829223 / 1000000) (27 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6970593 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6970593 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell226 :
    ∀ t ∈ Set.Icc ((799 / 2000) : ℝ) (801 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2223316499 / 1000000000) : ℝ) ≤ Real.exp (2 * (799 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (799 / 2000)) (2223316499 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((801 / 2000) : ℝ)) ≤ (2227767583 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (801 / 2000)) (2227767583 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((248099823610393 / 200000) : ℝ) ≤ Real.exp (3 * (1746137 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1746137 / 250000)) (248099823610393 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((799 / 2000) : ℝ) (801 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1746137 / 250000) (1399751 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (799 / 2000) (801 / 2000) (2223316499 / 1000000000) (2227767583 / 1000000000) (1746137 / 250000) (1399751 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (799 / 2000) (801 / 2000) (1746137 / 250000) (1399751 / 200000) (153143 / 1000) (154023 / 1000)
    (1361159 / 1000) (1384001 / 1000) (4023361 / 500) (143 / 1000000) (19194339 / 500) (207 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1746137 / 250000) (248099823610393 / 200000) (207 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1746137 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1746137 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell227 :
    ∀ t ∈ Set.Icc ((801 / 2000) : ℝ) (803 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1113883791 / 500000000) : ℝ) ≤ Real.exp (2 * (801 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (801 / 2000)) (1113883791 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((803 / 2000) : ℝ)) ≤ (2232227577 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (803 / 2000)) (2232227577 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((646577339805077 / 500000) : ℝ) ≤ Real.exp (3 * (6998531 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6998531 / 1000000)) (646577339805077 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((801 / 2000) : ℝ) (803 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6998531 / 1000000) (7012767 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (801 / 2000) (803 / 2000) (1113883791 / 500000000) (2232227577 / 1000000000) (6998531 / 1000000) (7012767 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (801 / 2000) (803 / 2000) (6998531 / 1000000) (7012767 / 1000000) (153841 / 1000) (6189 / 40)
    (1371883 / 1000) (27897 / 20) (2039321 / 250) (69 / 500000) (38697029 / 1000) (99 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6998531 / 1000000) (646577339805077 / 500000) (99 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6998531 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6998531 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell228 :
    ∀ t ∈ Set.Icc ((803 / 2000) : ℝ) (161 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((279028447 / 125000000) : ℝ) ≤ Real.exp (2 * (803 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (803 / 2000)) (279028447 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((161 / 400) : ℝ)) ≤ (2236696499 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (161 / 400)) (2236696499 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1348147014216633 / 1000000) : ℝ) ≤ Real.exp (3 * (3506271 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3506271 / 500000)) (1348147014216633 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((803 / 2000) : ℝ) (161 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3506271 / 500000) (3513403 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (803 / 2000) (161 / 400) (279028447 / 125000000) (2236696499 / 1000000000) (3506271 / 500000) (3513403 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (803 / 2000) (161 / 400) (3506271 / 500000) (3513403 / 500000) (77271 / 500) (155429 / 1000)
    (1382683 / 1000) (56231 / 40) (8269043 / 1000) (133 / 1000000) (7801567 / 200) (19 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3506271 / 500000) (1348147014216633 / 1000000) (19 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3506271 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3506271 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell229 :
    ∀ t ∈ Set.Icc ((161 / 400) : ℝ) (807 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1118348249 / 500000000) : ℝ) ≤ Real.exp (2 * (161 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (161 / 400)) (1118348249 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((807 / 2000) : ℝ)) ≤ (2241174369 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (807 / 2000)) (2241174369 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((702793958538923 / 500000) : ℝ) ≤ Real.exp (3 * (3513291 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3513291 / 500000)) (702793958538923 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((161 / 400) : ℝ) (807 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3513291 / 500000) (3520437 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (161 / 400) (807 / 2000) (1118348249 / 500000000) (2241174369 / 1000000000) (3513291 / 500000) (3520437 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (161 / 400) (807 / 2000) (3513291 / 500000) (3520437 / 500000) (77623 / 500) (156137 / 1000)
    (34839 / 25) (1416777 / 1000) (2095511 / 250) (129 / 1000000) (9830289 / 250) (183 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3513291 / 500000) (702793958538923 / 500000) (183 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3513291 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3513291 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell230 :
    ∀ t ∈ Set.Icc ((807 / 2000) : ℝ) (809 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((70036699 / 31250000) : ℝ) ≤ Real.exp (2 * (807 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (807 / 2000)) (70036699 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((809 / 2000) : ℝ)) ≤ (2245661203 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (809 / 2000)) (2245661203 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((366395485954213 / 250000) : ℝ) ≤ Real.exp (3 * (7040649 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (7040649 / 1000000)) (366395485954213 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((807 / 2000) : ℝ) (809 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (7040649 / 1000000) (705497 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (807 / 2000) (809 / 2000) (70036699 / 31250000) (2245661203 / 1000000000) (7040649 / 1000000) (705497 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (807 / 2000) (809 / 2000) (7040649 / 1000000) (705497 / 100000) (155953 / 1000) (156847 / 1000)
    (1404513 / 1000) (1427857 / 1000) (8496307 / 1000) (31 / 250000) (39636991 / 1000) (7 / 40000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (7040649 / 1000000) (366395485954213 / 250000) (7 / 40000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7040649 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7040649 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell231 :
    ∀ t ∈ Set.Icc ((809 / 2000) : ℝ) (811 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1122830601 / 500000000) : ℝ) ≤ Real.exp (2 * (809 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (809 / 2000)) (1122830601 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((811 / 2000) : ℝ)) ≤ (2250157019 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (811 / 2000)) (2250157019 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1528251196096649 / 1000000) : ℝ) ≤ Real.exp (3 * (881843 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (881843 / 125000)) (1528251196096649 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((809 / 2000) : ℝ) (811 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (881843 / 125000) (3534547 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (809 / 2000) (811 / 2000) (1122830601 / 500000000) (2250157019 / 1000000000) (881843 / 125000) (3534547 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (809 / 2000) (811 / 2000) (881843 / 125000) (3534547 / 500000) (156663 / 1000) (3939 / 25)
    (707771 / 500) (719507 / 500) (8611827 / 1000) (3 / 25000) (39955357 / 1000) (21 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (881843 / 125000) (1528251196096649 / 1000000) (21 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (881843 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (881843 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell232 :
    ∀ t ∈ Set.Icc ((811 / 2000) : ℝ) (813 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1125078509 / 500000000) : ℝ) ≤ Real.exp (2 * (811 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (811 / 2000)) (1125078509 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((813 / 2000) : ℝ)) ≤ (2254661837 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (813 / 2000)) (2254661837 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((199215515787933 / 125000) : ℝ) ≤ Real.exp (3 * (1767217 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1767217 / 250000)) (199215515787933 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((811 / 2000) : ℝ) (813 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1767217 / 250000) (3541623 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (811 / 2000) (813 / 2000) (1125078509 / 500000000) (2254661837 / 1000000000) (1767217 / 250000) (3541623 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (811 / 2000) (813 / 2000) (1767217 / 250000) (3541623 / 500000) (19672 / 125) (158277 / 1000)
    (1426649 / 1000) (181281 / 125) (8728599 / 1000) (23 / 200000) (20138137 / 500) (161 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1767217 / 250000) (199215515787933 / 125000) (161 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1767217 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1767217 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell233 :
    ∀ t ∈ Set.Icc ((813 / 2000) : ℝ) (163 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((563665459 / 250000000) : ℝ) ≤ Real.exp (2 * (813 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (813 / 2000)) (563665459 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((163 / 400) : ℝ)) ≤ (2259175673 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (163 / 400)) (2259175673 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((51941438267317 / 31250) : ℝ) ≤ Real.exp (3 * (354151 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (354151 / 50000)) (51941438267317 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((813 / 2000) : ℝ) (163 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (354151 / 50000) (7097427 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (813 / 2000) (163 / 400) (563665459 / 250000000) (2259175673 / 1000000000) (354151 / 50000) (7097427 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (813 / 2000) (163 / 400) (354151 / 50000) (7097427 / 1000000) (39523 / 250) (39749 / 250)
    (287567 / 200) (1461563 / 1000) (8846677 / 1000) (7 / 62500) (5074973 / 125) (31 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (354151 / 50000) (51941438267317 / 31250) (31 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (354151 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (354151 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell234 :
    ∀ t ∈ Set.Icc ((163 / 400) : ℝ) (817 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((282396959 / 125000000) : ℝ) ≤ Real.exp (2 * (163 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (163 / 400)) (282396959 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((817 / 2000) : ℝ)) ≤ (1131849273 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (817 / 2000)) (1131849273 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((346718544975541 / 200000) : ℝ) ≤ Real.exp (3 * (17743 / 2500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (17743 / 2500)) (346718544975541 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((163 / 400) : ℝ) (817 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (17743 / 2500) (1777909 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (163 / 400) (817 / 2000) (282396959 / 125000000) (1131849273 / 500000000) (17743 / 2500) (1777909 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (163 / 400) (817 / 2000) (17743 / 2500) (1777909 / 250000) (158811 / 1000) (159719 / 1000)
    (724549 / 500) (368239 / 250) (8966049 / 1000) (107 / 1000000) (10231471 / 250) (37 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (17743 / 2500) (346718544975541 / 200000) (37 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (17743 / 2500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (17743 / 2500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell235 :
    ∀ t ∈ Set.Icc ((817 / 2000) : ℝ) (819 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((141481159 / 62500000) : ℝ) ≤ Real.exp (2 * (817 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (817 / 2000)) (141481159 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((819 / 2000) : ℝ)) ≤ (2268230473 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (819 / 2000)) (2268230473 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1808266554195223 / 1000000) : ℝ) ≤ Real.exp (3 * (444463 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (444463 / 62500)) (1808266554195223 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((817 / 2000) : ℝ) (819 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (444463 / 62500) (7125873 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (817 / 2000) (819 / 2000) (141481159 / 62500000) (2268230473 / 1000000000) (444463 / 62500) (7125873 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (817 / 2000) (819 / 2000) (444463 / 62500) (7125873 / 1000000) (159533 / 1000) (40111 / 250)
    (1460441 / 1000) (1484429 / 1000) (9086727 / 1000) (13 / 125000) (5156824 / 125) (71 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (444463 / 62500) (1808266554195223 / 1000000) (71 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (444463 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (444463 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell236 :
    ∀ t ∈ Set.Icc ((819 / 2000) : ℝ) (821 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((283528809 / 125000000) : ℝ) ≤ Real.exp (2 * (819 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (819 / 2000)) (283528809 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((821 / 2000) : ℝ)) ≤ (1136385737 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (821 / 2000)) (1136385737 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((943153922521133 / 500000) : ℝ) ≤ Real.exp (3 * (3562823 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3562823 / 500000)) (943153922521133 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((819 / 2000) : ℝ) (821 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3562823 / 500000) (7140139 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (819 / 2000) (821 / 2000) (283528809 / 125000000) (1136385737 / 500000000) (3562823 / 500000) (7140139 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (819 / 2000) (821 / 2000) (3562823 / 500000) (7140139 / 1000000) (80129 / 500) (161173 / 1000)
    (183983 / 125) (747991 / 500) (4604357 / 500) (1 / 10000) (41585953 / 1000) (17 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3562823 / 500000) (943153922521133 / 500000) (17 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3562823 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3562823 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell237 :
    ∀ t ∈ Set.Icc ((821 / 2000) : ℝ) (823 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((142048217 / 62500000) : ℝ) ≤ Real.exp (2 * (821 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (821 / 2000)) (142048217 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((823 / 2000) : ℝ)) ≤ (455464313 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (823 / 2000)) (455464313 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((393571362320113 / 200000) : ℝ) ≤ Real.exp (3 * (7139911 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (7139911 / 1000000)) (393571362320113 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((821 / 2000) : ℝ) (823 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (7139911 / 1000000) (3577217 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (821 / 2000) (823 / 2000) (142048217 / 62500000) (455464313 / 200000000) (7139911 / 1000000) (3577217 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (821 / 2000) (823 / 2000) (7139911 / 1000000) (3577217 / 500000) (80493 / 500) (32381 / 200)
    (741683 / 500) (753809 / 500) (4666037 / 500) (97 / 1000000) (8383997 / 200) (131 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (7139911 / 1000000) (393571362320113 / 200000) (131 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7139911 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7139911 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell238 :
    ∀ t ∈ Set.Icc ((823 / 2000) : ℝ) (33 / 80), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((569330391 / 250000000) : ℝ) ≤ Real.exp (2 * (823 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (823 / 2000)) (569330391 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((33 / 80) : ℝ)) ≤ (1140940383 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (33 / 80)) (1140940383 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2053088723113771 / 1000000) : ℝ) ≤ Real.exp (3 * (1430841 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1430841 / 200000)) (2053088723113771 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((823 / 2000) : ℝ) (33 / 80),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1430841 / 200000) (7168757 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (823 / 2000) (33 / 80) (569330391 / 250000000) (1140940383 / 500000000) (1430841 / 200000) (7168757 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (823 / 2000) (33 / 80) (1430841 / 200000) (7168757 / 1000000) (80859 / 500) (4066 / 25)
    (29899 / 20) (759667 / 500) (236419 / 25) (93 / 1000000) (8451337 / 200) (1 / 8000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1430841 / 200000) (2053088723113771 / 1000000) (1 / 8000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1430841 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1430841 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell239 :
    ∀ t ∈ Set.Icc ((33 / 80) : ℝ) (827 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((456376153 / 200000000) : ℝ) ≤ Real.exp (2 * (33 / 80)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (33 / 80)) (456376153 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((827 / 2000) : ℝ)) ≤ (1143224547 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (827 / 2000)) (1143224547 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2142176048187357 / 1000000) : ℝ) ≤ Real.exp (3 * (448033 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (448033 / 62500)) (2142176048187357 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((33 / 80) : ℝ) (827 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (448033 / 62500) (7183109 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (33 / 80) (827 / 2000) (456376153 / 200000000) (1143224547 / 500000000) (448033 / 62500) (7183109 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (33 / 80) (827 / 2000) (448033 / 62500) (7183109 / 1000000) (40613 / 250) (81689 / 500)
    (753307 / 500) (1531131 / 1000) (958281 / 100) (9 / 100000) (21298049 / 500) (3 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (448033 / 62500) (2142176048187357 / 1000000) (3 / 25000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (448033 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (448033 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityUpperExpCompact_cellsBatch011 :
    ∀ t ∈ Set.Icc ((787 / 2000) : ℝ) (827 / 2000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell220
      hpThetaDensityUpperExpCompact_cell221)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell222
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell223
      hpThetaDensityUpperExpCompact_cell224)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell225
      hpThetaDensityUpperExpCompact_cell226)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell227
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell228
      hpThetaDensityUpperExpCompact_cell229))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell230
      hpThetaDensityUpperExpCompact_cell231)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell232
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell233
      hpThetaDensityUpperExpCompact_cell234)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell235
      hpThetaDensityUpperExpCompact_cell236)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell237
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell238
      hpThetaDensityUpperExpCompact_cell239)))))

#print axioms hpThetaDensityUpperExpCompact_cellsBatch011
end HodgeProofHP
