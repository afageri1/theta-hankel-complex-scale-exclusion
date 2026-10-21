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
theorem hpThetaDensityUpperExpCompact_cell200 :
    ∀ t ∈ Set.Icc ((747 / 2000) : ℝ) (749 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2110658533 / 1000000000) : ℝ) ≤ Real.exp (2 * (747 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (747 / 2000)) (2110658533 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((749 / 2000) : ℝ)) ≤ (84595363 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (749 / 2000)) (84595363 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((108044017217621 / 250000) : ℝ) ≤ Real.exp (3 * (6630633 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6630633 / 1000000)) (108044017217621 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((747 / 2000) : ℝ) (749 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6630633 / 1000000) (166103 / 25000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (747 / 2000) (749 / 2000) (2110658533 / 1000000000) (84595363 / 40000000) (6630633 / 1000000) (166103 / 25000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (747 / 2000) (749 / 2000) (6630633 / 1000000) (166103 / 25000) (33999 / 250) (68397 / 500)
    (1107271 / 1000) (225421 / 200) (5564731 / 1000) (7 / 20000) (31179551 / 1000) (593 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6630633 / 1000000) (108044017217621 / 250000) (593 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6630633 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6630633 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell201 :
    ∀ t ∈ Set.Icc ((749 / 2000) : ℝ) (751 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1057442037 / 500000000) : ℝ) ≤ Real.exp (2 * (749 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (749 / 2000)) (1057442037 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((751 / 2000) : ℝ)) ≤ (529779519 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (751 / 2000)) (529779519 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((449642281147551 / 1000000) : ℝ) ≤ Real.exp (3 * (1660977 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1660977 / 250000)) (449642281147551 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((749 / 2000) : ℝ) (751 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1660977 / 250000) (3328711 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (749 / 2000) (751 / 2000) (1057442037 / 500000000) (529779519 / 250000000) (1660977 / 250000) (3328711 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (749 / 2000) (751 / 2000) (1660977 / 250000) (3328711 / 500000) (136621 / 1000) (68711 / 500)
    (1116197 / 1000) (1136139 / 1000) (2823689 / 500) (169 / 500000) (31429997 / 1000) (57 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1660977 / 250000) (449642281147551 / 1000000) (57 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1660977 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1660977 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell202 :
    ∀ t ∈ Set.Icc ((751 / 2000) : ℝ) (753 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((84764723 / 40000000) : ℝ) ≤ Real.exp (2 * (751 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (751 / 2000)) (84764723 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((753 / 2000) : ℝ)) ≤ (2123360553 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (753 / 2000)) (2123360553 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((11696212653783 / 25000) : ℝ) ≤ Real.exp (3 * (6657209 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6657209 / 1000000)) (11696212653783 / 25000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((751 / 2000) : ℝ) (753 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6657209 / 1000000) (26683 / 4000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (751 / 2000) (753 / 2000) (84764723 / 40000000) (2123360553 / 1000000000) (6657209 / 1000000) (26683 / 4000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (751 / 2000) (753 / 2000) (6657209 / 1000000) (26683 / 4000) (137249 / 1000) (138053 / 1000)
    (1125187 / 1000) (1145237 / 1000) (1146193 / 200) (327 / 1000000) (15841221 / 500) (137 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6657209 / 1000000) (11696212653783 / 25000) (137 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6657209 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6657209 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell203 :
    ∀ t ∈ Set.Icc ((753 / 2000) : ℝ) (151 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((265420069 / 125000000) : ℝ) ≤ Real.exp (2 * (753 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (753 / 2000)) (265420069 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((151 / 400) : ℝ)) ≤ (531902881 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (151 / 400)) (531902881 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((243414408678617 / 500000) : ℝ) ≤ Real.exp (3 * (6670537 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6670537 / 1000000)) (243414408678617 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((753 / 2000) : ℝ) (151 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6670537 / 1000000) (1336821 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (753 / 2000) (151 / 400) (265420069 / 125000000) (531902881 / 250000000) (6670537 / 1000000) (1336821 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (753 / 2000) (151 / 400) (6670537 / 1000000) (1336821 / 200000) (137879 / 1000) (69343 / 500)
    (1134241 / 1000) (5772 / 5) (1453877 / 250) (79 / 250000) (31936921 / 1000) (263 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6670537 / 1000000) (243414408678617 / 500000) (263 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6670537 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6670537 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell204 :
    ∀ t ∈ Set.Icc ((151 / 400) : ℝ) (757 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2127611523 / 1000000000) : ℝ) ≤ Real.exp (2 * (151 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (151 / 400)) (2127611523 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((757 / 2000) : ℝ)) ≤ (426374201 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (757 / 2000)) (426374201 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((506615988236759 / 1000000) : ℝ) ≤ Real.exp (3 * (6683891 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6683891 / 1000000)) (506615988236759 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((151 / 400) : ℝ) (757 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6683891 / 1000000) (3348743 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (151 / 400) (757 / 2000) (2127611523 / 1000000000) (426374201 / 200000000) (6683891 / 1000000) (3348743 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (151 / 400) (757 / 2000) (6683891 / 1000000) (3348743 / 500000) (17314 / 125) (69661 / 500)
    (1143359 / 1000) (1163627 / 1000) (5901009 / 1000) (153 / 500000) (3219343 / 100) (253 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6683891 / 1000000) (506615988236759 / 1000000) (253 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6683891 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6683891 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell205 :
    ∀ t ∈ Set.Icc ((757 / 2000) : ℝ) (759 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((532967751 / 250000000) : ℝ) ≤ Real.exp (2 * (757 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (757 / 2000)) (532967751 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((759 / 2000) : ℝ)) ≤ (1068069507 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (759 / 2000)) (1068069507 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((527247264369267 / 1000000) : ℝ) ≤ Real.exp (3 * (837159 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (837159 / 125000)) (527247264369267 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((757 / 2000) : ℝ) (759 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (837159 / 125000) (1342179 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (757 / 2000) (759 / 2000) (532967751 / 250000000) (1068069507 / 500000000) (837159 / 125000) (1342179 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (757 / 2000) (759 / 2000) (837159 / 125000) (1342179 / 200000) (34787 / 250) (139961 / 1000)
    (1152541 / 1000) (1172921 / 1000) (5987507 / 1000) (59 / 200000) (16226011 / 500) (243 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (837159 / 125000) (527247264369267 / 1000000) (243 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (837159 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (837159 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell206 :
    ∀ t ∈ Set.Icc ((759 / 2000) : ℝ) (761 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((534034753 / 250000000) : ℝ) ≤ Real.exp (2 * (759 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (759 / 2000)) (534034753 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((761 / 2000) : ℝ)) ≤ (2140415567 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (761 / 2000)) (2140415567 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((548760141185659 / 1000000) : ℝ) ≤ Real.exp (3 * (167767 / 25000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (167767 / 25000)) (548760141185659 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((759 / 2000) : ℝ) (761 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (167767 / 25000) (672433 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (759 / 2000) (761 / 2000) (534034753 / 250000000) (2140415567 / 1000000000) (167767 / 25000) (672433 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (759 / 2000) (761 / 2000) (167767 / 25000) (672433 / 100000) (69893 / 500) (140603 / 1000)
    (116179 / 100) (29557 / 25) (3037483 / 500) (143 / 500000) (1308507 / 40) (467 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (167767 / 25000) (548760141185659 / 1000000) (467 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (167767 / 25000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (167767 / 25000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell207 :
    ∀ t ∈ Set.Icc ((761 / 2000) : ℝ) (763 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1070207783 / 500000000) : ℝ) ≤ Real.exp (2 * (761 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (761 / 2000)) (1070207783 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((763 / 2000) : ℝ)) ≤ (1072350341 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (763 / 2000)) (1072350341 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((114238767567849 / 200000) : ℝ) ≤ Real.exp (3 * (1344823 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1344823 / 200000)) (114238767567849 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((761 / 2000) : ℝ) (763 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1344823 / 200000) (105278 / 15625) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (761 / 2000) (763 / 2000) (1070207783 / 500000000) (1072350341 / 500000000) (1344823 / 200000) (105278 / 15625) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (761 / 2000) (763 / 2000) (1344823 / 200000) (105278 / 15625) (35107 / 250) (141247 / 1000)
    (146388 / 125) (238341 / 200) (6163419 / 1000) (69 / 250000) (4121928 / 125) (449 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1344823 / 200000) (114238767567849 / 200000) (449 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1344823 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1344823 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell208 :
    ∀ t ∈ Set.Icc ((763 / 2000) : ℝ) (153 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((53617517 / 25000000) : ℝ) ≤ Real.exp (2 * (763 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (763 / 2000)) (53617517 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((153 / 400) : ℝ)) ≤ (3438391 / 1600000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (153 / 400)) (3438391 / 1600000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((594589378799149 / 1000000) : ℝ) ≤ Real.exp (3 * (6737577 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6737577 / 1000000)) (594589378799149 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((763 / 2000) : ℝ) (153 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6737577 / 1000000) (6751281 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (763 / 2000) (153 / 400) (53617517 / 25000000) (3438391 / 1600000) (6737577 / 1000000) (6751281 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (763 / 2000) (153 / 400) (6737577 / 1000000) (6751281 / 1000000) (17634 / 125) (70947 / 500)
    (236097 / 200) (1201197 / 1000) (50023 / 8) (267 / 1000000) (8310071 / 250) (431 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6737577 / 1000000) (594589378799149 / 1000000) (431 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6737577 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6737577 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell209 :
    ∀ t ∈ Set.Icc ((153 / 400) : ℝ) (767 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1074497187 / 500000000) : ℝ) ≤ Real.exp (2 * (153 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (153 / 400)) (1074497187 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((767 / 2000) : ℝ)) ≤ (430659333 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (767 / 2000)) (430659333 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((123797566801731 / 200000) : ℝ) ≤ Real.exp (3 * (1350213 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1350213 / 200000)) (123797566801731 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((153 / 400) : ℝ) (767 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1350213 / 200000) (6764797 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (153 / 400) (767 / 2000) (1074497187 / 500000000) (430659333 / 200000000) (1350213 / 200000) (6764797 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (153 / 400) (767 / 2000) (1350213 / 200000) (6764797 / 1000000) (70859 / 500) (17818 / 125)
    (1189931 / 1000) (1210757 / 1000) (6343359 / 1000) (129 / 500000) (33507271 / 1000) (207 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1350213 / 200000) (123797566801731 / 200000) (207 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1350213 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1350213 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell210 :
    ∀ t ∈ Set.Icc ((767 / 2000) : ℝ) (769 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((269162083 / 125000000) : ℝ) ≤ Real.exp (2 * (767 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (767 / 2000)) (269162083 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((769 / 2000) : ℝ)) ≤ (134850473 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (769 / 2000)) (134850473 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((644437714562019 / 1000000) : ℝ) ≤ Real.exp (3 * (6764581 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6764581 / 1000000)) (644437714562019 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((767 / 2000) : ℝ) (769 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6764581 / 1000000) (338917 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (767 / 2000) (769 / 2000) (269162083 / 125000000) (134850473 / 62500000) (6764581 / 1000000) (338917 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (767 / 2000) (769 / 2000) (6764581 / 1000000) (338917 / 50000) (17796 / 125) (143197 / 1000)
    (239889 / 200) (152548 / 125) (128697 / 20) (249 / 1000000) (16888201 / 500) (199 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6764581 / 1000000) (644437714562019 / 1000000) (199 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6764581 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6764581 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell211 :
    ∀ t ∈ Set.Icc ((769 / 2000) : ℝ) (771 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1078803783 / 500000000) : ℝ) ≤ Real.exp (2 * (769 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (769 / 2000)) (1078803783 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((771 / 2000) : ℝ)) ≤ (2161927101 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (771 / 2000)) (2161927101 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((335492108996953 / 500000) : ℝ) ≤ Real.exp (3 * (1694531 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1694531 / 250000)) (335492108996953 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((769 / 2000) : ℝ) (771 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1694531 / 250000) (6791911 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (769 / 2000) (771 / 2000) (1078803783 / 500000000) (2161927101 / 1000000000) (1694531 / 250000) (6791911 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (769 / 2000) (771 / 2000) (1694531 / 250000) (6791911 / 1000000) (7151 / 50) (35963 / 250)
    (1209027 / 1000) (30752 / 25) (1305479 / 200) (241 / 1000000) (4255964 / 125) (191 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1694531 / 250000) (335492108996953 / 500000) (191 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1694531 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1694531 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell212 :
    ∀ t ∈ Set.Icc ((771 / 2000) : ℝ) (773 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((21619271 / 10000000) : ℝ) ≤ Real.exp (2 * (771 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (771 / 2000)) (21619271 / 10000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((773 / 2000) : ℝ)) ≤ (1083127641 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (773 / 2000)) (1083127641 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((69867440592859 / 100000) : ℝ) ≤ Real.exp (3 * (6791693 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6791693 / 1000000)) (69867440592859 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((771 / 2000) : ℝ) (773 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6791693 / 1000000) (1701377 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (771 / 2000) (773 / 2000) (21619271 / 10000000) (1083127641 / 500000000) (6791693 / 1000000) (1701377 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (771 / 2000) (773 / 2000) (6791693 / 1000000) (1701377 / 250000) (5747 / 40) (14451 / 100)
    (48747 / 40) (309961 / 250) (827622 / 125) (233 / 1000000) (17160589 / 500) (367 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6791693 / 1000000) (69867440592859 / 100000) (367 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6791693 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6791693 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell213 :
    ∀ t ∈ Set.Icc ((773 / 2000) : ℝ) (31 / 80), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2166255281 / 1000000000) : ℝ) ≤ Real.exp (2 * (773 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (773 / 2000)) (2166255281 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((31 / 80) : ℝ)) ≤ (16957751 / 7812500) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (31 / 80)) (16957751 / 7812500) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((145512755444727 / 200000) : ℝ) ≤ Real.exp (3 * (680529 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (680529 / 100000)) (145512755444727 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((773 / 2000) : ℝ) (31 / 80),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (680529 / 100000) (6819133 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (773 / 2000) (31 / 80) (2166255281 / 1000000000) (16957751 / 7812500) (680529 / 100000) (6819133 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (773 / 2000) (31 / 80) (680529 / 100000) (6819133 / 1000000) (144333 / 1000) (145171 / 1000)
    (1228393 / 1000) (1249677 / 1000) (839452 / 125) (9 / 40000) (4324607 / 125) (11 / 31250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (680529 / 100000) (145512755444727 / 200000) (11 / 31250000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (680529 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (680529 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell214 :
    ∀ t ∈ Set.Icc ((31 / 80) : ℝ) (777 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2170592127 / 1000000000) : ℝ) ≤ Real.exp (2 * (31 / 80)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (31 / 80)) (2170592127 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((777 / 2000) : ℝ)) ≤ (271867207 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (777 / 2000)) (271867207 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((757706394906833 / 1000000) : ℝ) ≤ Real.exp (3 * (1363783 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1363783 / 200000)) (757706394906833 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((31 / 80) : ℝ) (777 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1363783 / 200000) (1366557 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (31 / 80) (777 / 2000) (2170592127 / 1000000000) (271867207 / 125000000) (1363783 / 200000) (1366557 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (31 / 80) (777 / 2000) (1363783 / 200000) (1366557 / 200000) (144993 / 1000) (29167 / 200)
    (61909 / 50) (1259579 / 1000) (3405651 / 500) (217 / 1000000) (34874743 / 1000) (169 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1363783 / 200000) (757706394906833 / 1000000) (169 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1363783 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1363783 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell215 :
    ∀ t ∈ Set.Icc ((777 / 2000) : ℝ) (779 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((434987531 / 200000000) : ℝ) ≤ Real.exp (2 * (777 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (777 / 2000)) (434987531 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((779 / 2000) : ℝ)) ≤ (544822971 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (779 / 2000)) (544822971 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((9864426777527 / 12500) : ℝ) ≤ Real.exp (3 * (3416283 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3416283 / 500000)) (9864426777527 / 12500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((777 / 2000) : ℝ) (779 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3416283 / 500000) (106976 / 15625) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (777 / 2000) (779 / 2000) (434987531 / 200000000) (544822971 / 250000000) (3416283 / 500000) (106976 / 15625) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (777 / 2000) (779 / 2000) (3416283 / 500000) (106976 / 15625) (145657 / 1000) (146501 / 1000)
    (312009 / 250) (158694 / 125) (6908077 / 1000) (21 / 100000) (17577427 / 500) (13 / 40000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3416283 / 500000) (9864426777527 / 12500) (13 / 40000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3416283 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3416283 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell216 :
    ∀ t ∈ Set.Icc ((779 / 2000) : ℝ) (781 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2179291883 / 1000000000) : ℝ) ≤ Real.exp (2 * (779 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (779 / 2000)) (2179291883 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((781 / 2000) : ℝ)) ≤ (2183654829 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (781 / 2000)) (2183654829 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((20549263953591 / 25000) : ℝ) ≤ Real.exp (3 * (1369249 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1369249 / 200000)) (20549263953591 / 25000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((779 / 2000) : ℝ) (781 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1369249 / 200000) (6860171 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (779 / 2000) (781 / 2000) (2179291883 / 1000000000) (2183654829 / 1000000000) (1369249 / 200000) (6860171 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (779 / 2000) (781 / 2000) (1369249 / 200000) (6860171 / 1000000) (146323 / 1000) (147171 / 1000)
    (1257961 / 1000) (255919 / 200) (7005943 / 1000) (203 / 1000000) (35437229 / 1000) (39 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1369249 / 200000) (20549263953591 / 25000) (39 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1369249 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1369249 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell217 :
    ∀ t ∈ Set.Icc ((781 / 2000) : ℝ) (783 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((545913707 / 250000000) : ℝ) ≤ Real.exp (2 * (781 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (781 / 2000)) (545913707 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((783 / 2000) : ℝ)) ≤ (2188026509 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (783 / 2000)) (2188026509 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((856215064555169 / 1000000) : ℝ) ≤ Real.exp (3 * (6859951 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6859951 / 1000000)) (856215064555169 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((781 / 2000) : ℝ) (783 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6859951 / 1000000) (1374781 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (781 / 2000) (783 / 2000) (545913707 / 250000000) (2188026509 / 1000000000) (6859951 / 1000000) (1374781 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (781 / 2000) (783 / 2000) (6859951 / 1000000) (1374781 / 200000) (18374 / 125) (147843 / 1000)
    (1267957 / 1000) (1289709 / 1000) (7104901 / 1000) (49 / 250000) (17860931 / 500) (299 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6859951 / 1000000) (856215064555169 / 1000000) (299 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6859951 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6859951 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell218 :
    ∀ t ∈ Set.Icc ((783 / 2000) : ℝ) (157 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((547006627 / 250000000) : ℝ) ≤ Real.exp (2 * (783 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (783 / 2000)) (547006627 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((157 / 400) : ℝ)) ≤ (2192406941 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (157 / 400)) (2192406941 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((445977435942147 / 500000) : ℝ) ≤ Real.exp (3 * (1374737 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1374737 / 200000)) (445977435942147 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((783 / 2000) : ℝ) (157 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1374737 / 200000) (3443833 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (783 / 2000) (157 / 400) (547006627 / 250000000) (2192406941 / 1000000000) (1374737 / 200000) (3443833 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (783 / 2000) (157 / 400) (1374737 / 200000) (3443833 / 500000) (18458 / 125) (74259 / 500)
    (159753 / 125) (1299893 / 1000) (7204947 / 1000) (189 / 1000000) (36008771 / 1000) (9 / 31250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1374737 / 200000) (445977435942147 / 500000) (9 / 31250000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1374737 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1374737 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell219 :
    ∀ t ∈ Set.Icc ((157 / 400) : ℝ) (787 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((109620347 / 50000000) : ℝ) ≤ Real.exp (2 * (157 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (157 / 400)) (109620347 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((787 / 2000) : ℝ)) ≤ (2196796143 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (787 / 2000)) (2196796143 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((929255113935129 / 1000000) : ℝ) ≤ Real.exp (3 * (3443723 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3443723 / 500000)) (929255113935129 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((157 / 400) : ℝ) (787 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3443723 / 500000) (1380291 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (157 / 400) (787 / 2000) (109620347 / 50000000) (2196796143 / 1000000000) (3443723 / 500000) (1380291 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (157 / 400) (787 / 2000) (3443723 / 500000) (1380291 / 200000) (74169 / 500) (37299 / 250)
    (644081 / 500) (26203 / 20) (7306131 / 1000) (183 / 1000000) (7259599 / 200) (69 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3443723 / 500000) (929255113935129 / 1000000) (69 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3443723 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3443723 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityUpperExpCompact_cellsBatch010 :
    ∀ t ∈ Set.Icc ((747 / 2000) : ℝ) (787 / 2000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell200
      hpThetaDensityUpperExpCompact_cell201)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell202
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell203
      hpThetaDensityUpperExpCompact_cell204)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell205
      hpThetaDensityUpperExpCompact_cell206)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell207
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell208
      hpThetaDensityUpperExpCompact_cell209))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell210
      hpThetaDensityUpperExpCompact_cell211)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell212
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell213
      hpThetaDensityUpperExpCompact_cell214)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell215
      hpThetaDensityUpperExpCompact_cell216)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell217
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell218
      hpThetaDensityUpperExpCompact_cell219)))))

#print axioms hpThetaDensityUpperExpCompact_cellsBatch010
end HodgeProofHP
