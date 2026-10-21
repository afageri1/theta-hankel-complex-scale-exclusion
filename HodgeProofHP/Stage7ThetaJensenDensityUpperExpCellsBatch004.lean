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
theorem hpThetaDensityUpperExpCompact_cell080 :
    ∀ t ∈ Set.Icc ((507 / 2000) : ℝ) (509 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1660302807 / 1000000000) : ℝ) ≤ Real.exp (2 * (507 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (507 / 2000)) (1660302807 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((509 / 2000) : ℝ)) ≤ (1663626737 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (509 / 2000)) (1663626737 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6245263809259 / 1000000) : ℝ) ≤ Real.exp (3 * (5215841 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5215841 / 1000000)) (6245263809259 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((507 / 2000) : ℝ) (509 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5215841 / 1000000) (104529 / 20000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (507 / 2000) (509 / 2000) (1660302807 / 1000000000) (1663626737 / 1000000000) (5215841 / 1000000) (104529 / 20000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (507 / 2000) (509 / 2000) (5215841 / 1000000) (104529 / 20000) (77461 / 1000) (77969 / 1000)
    (393939 / 1000) (101091 / 250) (178741 / 500) (1469 / 125000) (1193843 / 100) (1281 / 31250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5215841 / 1000000) (6245263809259 / 1000000) (1281 / 31250000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5215841 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5215841 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell081 :
    ∀ t ∈ Set.Icc ((509 / 2000) : ℝ) (511 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((103976671 / 62500000) : ℝ) ≤ Real.exp (2 * (509 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (509 / 2000)) (103976671 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((511 / 2000) : ℝ)) ≤ (41673933 / 25000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (511 / 2000)) (41673933 / 25000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((402747308151 / 62500) : ℝ) ≤ Real.exp (3 * (5226283 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5226283 / 1000000)) (402747308151 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((509 / 2000) : ℝ) (511 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5226283 / 1000000) (2618457 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (509 / 2000) (511 / 2000) (103976671 / 62500000) (41673933 / 25000000) (5226283 / 1000000) (2618457 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (509 / 2000) (511 / 2000) (5226283 / 1000000) (2618457 / 500000) (38917 / 500) (9793 / 125)
    (397643 / 1000) (408123 / 1000) (93853 / 250) (5729 / 500000) (6017163 / 500) (2483 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5226283 / 1000000) (402747308151 / 62500) (2483 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5226283 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5226283 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell082 :
    ∀ t ∈ Set.Icc ((511 / 2000) : ℝ) (513 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1666957319 / 1000000000) : ℝ) ≤ Real.exp (2 * (511 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (511 / 2000)) (1666957319 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((513 / 2000) : ℝ)) ≤ (167029457 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (513 / 2000)) (167029457 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((265975556619 / 40000) : ℝ) ≤ Real.exp (3 * (2618373 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2618373 / 500000)) (265975556619 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((511 / 2000) : ℝ) (513 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2618373 / 500000) (2623699 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (511 / 2000) (513 / 2000) (1666957319 / 1000000000) (167029457 / 100000000) (2618373 / 500000) (2623699 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (511 / 2000) (513 / 2000) (2618373 / 500000) (2623699 / 500000) (78209 / 1000) (78721 / 1000)
    (3211 / 8) (411911 / 1000) (393597 / 1000) (11171 / 1000000) (1516373 / 125) (77 / 2000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2618373 / 500000) (265975556619 / 40000) (77 / 2000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2618373 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2618373 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell083 :
    ∀ t ∈ Set.Icc ((513 / 2000) : ℝ) (103 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1670294569 / 1000000000) : ℝ) ≤ Real.exp (2 * (513 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (513 / 2000)) (1670294569 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((103 / 400) : ℝ)) ≤ (836819251 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (103 / 400)) (836819251 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1715450189399 / 250000) : ℝ) ≤ Real.exp (3 * (524723 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (524723 / 100000)) (1715450189399 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((513 / 2000) : ℝ) (103 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (524723 / 100000) (5257903 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (513 / 2000) (103 / 400) (1670294569 / 1000000000) (836819251 / 500000000) (524723 / 100000) (5257903 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (513 / 2000) (103 / 400) (524723 / 100000) (5257903 / 1000000) (39293 / 500) (79099 / 1000)
    (81027 / 200) (415727 / 1000) (412051 / 1000) (1089 / 100000) (6114209 / 500) (9327 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (524723 / 100000) (1715450189399 / 250000) (9327 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (524723 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (524723 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell084 :
    ∀ t ∈ Set.Icc ((103 / 400) : ℝ) (517 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1673638501 / 1000000000) : ℝ) ≤ Real.exp (2 * (103 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (103 / 400)) (1673638501 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((517 / 2000) : ℝ)) ≤ (1676989129 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (517 / 2000)) (1676989129 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((7081442470341 / 1000000) : ℝ) ≤ Real.exp (3 * (1051547 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1051547 / 200000)) (7081442470341 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((103 / 400) : ℝ) (517 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1051547 / 200000) (526843 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (103 / 400) (517 / 2000) (1673638501 / 1000000000) (1676989129 / 1000000000) (1051547 / 200000) (526843 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (103 / 400) (517 / 2000) (1051547 / 200000) (526843 / 100000) (19741 / 250) (1987 / 25)
    (102231 / 250) (419573 / 1000) (107697 / 250) (1327 / 125000) (3081661 / 250) (36151 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1051547 / 200000) (7081442470341 / 1000000) (36151 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1051547 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1051547 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell085 :
    ∀ t ∈ Set.Icc ((517 / 2000) : ℝ) (519 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((209623641 / 125000000) : ℝ) ≤ Real.exp (2 * (517 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (517 / 2000)) (209623641 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((519 / 2000) : ℝ)) ≤ (1680346463 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (519 / 2000)) (1680346463 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3654286719553 / 500000) : ℝ) ≤ Real.exp (3 * (5268261 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5268261 / 1000000)) (3654286719553 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((517 / 2000) : ℝ) (519 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5268261 / 1000000) (5278977 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (517 / 2000) (519 / 2000) (209623641 / 125000000) (1680346463 / 1000000000) (5268261 / 1000000) (5278977 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (517 / 2000) (519 / 2000) (5268261 / 1000000) (5278977 / 1000000) (9918 / 125) (79861 / 1000)
    (206371 / 500) (423447 / 1000) (449789 / 1000) (2587 / 250000) (12425649 / 1000) (8757 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5268261 / 1000000) (3654286719553 / 500000) (8757 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5268261 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5268261 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell086 :
    ∀ t ∈ Set.Icc ((519 / 2000) : ℝ) (521 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((840173231 / 500000000) : ℝ) ≤ Real.exp (2 * (519 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (519 / 2000)) (840173231 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((521 / 2000) : ℝ)) ≤ (1683710519 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (521 / 2000)) (1683710519 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1885865696683 / 250000) : ℝ) ≤ Real.exp (3 * (659851 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (659851 / 125000)) (1885865696683 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((519 / 2000) : ℝ) (521 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (659851 / 125000) (1057909 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (519 / 2000) (521 / 2000) (840173231 / 500000000) (1683710519 / 1000000000) (659851 / 125000) (1057909 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (519 / 2000) (521 / 2000) (659851 / 125000) (1057909 / 200000) (3189 / 40) (16049 / 200)
    (416589 / 1000) (427351 / 1000) (469067 / 1000) (5043 / 500000) (1565681 / 125) (33937 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (659851 / 125000) (1885865696683 / 250000) (33937 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (659851 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (659851 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell087 :
    ∀ t ∈ Set.Icc ((521 / 2000) : ℝ) (523 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((841855259 / 500000000) : ℝ) ≤ Real.exp (2 * (521 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (521 / 2000)) (841855259 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((523 / 2000) : ℝ)) ≤ (168708131 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (523 / 2000)) (168708131 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((7786389753897 / 1000000) : ℝ) ≤ Real.exp (3 * (165293 / 31250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (165293 / 31250)) (7786389753897 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((521 / 2000) : ℝ) (523 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (165293 / 31250) (1060027 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (521 / 2000) (523 / 2000) (841855259 / 500000000) (168708131 / 100000000) (165293 / 31250) (1060027 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (521 / 2000) (523 / 2000) (165293 / 31250) (1060027 / 200000) (80109 / 1000) (8063 / 100)
    (84093 / 200) (86257 / 200) (244319 / 500) (983 / 100000) (1578257 / 125) (16439 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (165293 / 31250) (7786389753897 / 1000000) (16439 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (165293 / 31250)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (165293 / 31250)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell088 :
    ∀ t ∈ Set.Icc ((523 / 2000) : ℝ) (21 / 80), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1687081309 / 1000000000) : ℝ) ≤ Real.exp (2 * (523 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (523 / 2000)) (1687081309 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((21 / 80) : ℝ)) ≤ (1690458849 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (21 / 80)) (1690458849 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2009411023727 / 250000) : ℝ) ≤ Real.exp (3 * (1059993 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1059993 / 200000)) (2009411023727 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((523 / 2000) : ℝ) (21 / 80),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1059993 / 200000) (2655373 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (523 / 2000) (21 / 80) (1687081309 / 1000000000) (1690458849 / 1000000000) (1059993 / 200000) (2655373 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (523 / 2000) (21 / 80) (1059993 / 200000) (2655373 / 500000) (40247 / 500) (81017 / 1000)
    (424371 / 1000) (54406 / 125) (508493 / 1000) (479 / 50000) (12727471 / 1000) (31851 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1059993 / 200000) (2009411023727 / 250000) (31851 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1059993 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1059993 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell089 :
    ∀ t ∈ Set.Icc ((21 / 80) : ℝ) (527 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((52826839 / 31250000) : ℝ) ≤ Real.exp (2 * (21 / 80)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (21 / 80)) (52826839 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((527 / 2000) : ℝ)) ≤ (33876863 / 20000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (527 / 2000)) (33876863 / 20000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8297551375343 / 1000000) : ℝ) ≤ Real.exp (3 * (331911 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (331911 / 62500)) (8297551375343 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((21 / 80) : ℝ) (527 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (331911 / 62500) (2660689 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (21 / 80) (527 / 2000) (52826839 / 31250000) (33876863 / 20000000) (331911 / 62500) (2660689 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (21 / 80) (527 / 2000) (331911 / 62500) (2660689 / 500000) (2022 / 25) (16281 / 200)
    (214153 / 500) (439241 / 1000) (4229 / 8) (1167 / 125000) (6414849 / 500) (30853 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (331911 / 62500) (8297551375343 / 1000000) (30853 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (331911 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (331911 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell090 :
    ∀ t ∈ Set.Icc ((527 / 2000) : ℝ) (529 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1693843149 / 1000000000) : ℝ) ≤ Real.exp (2 * (527 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (527 / 2000)) (1693843149 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((529 / 2000) : ℝ)) ≤ (848617113 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (529 / 2000)) (848617113 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((856640035527 / 100000) : ℝ) ≤ Real.exp (3 * (665151 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (665151 / 125000)) (856640035527 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((527 / 2000) : ℝ) (529 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (665151 / 125000) (83313 / 15625) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (527 / 2000) (529 / 2000) (1693843149 / 1000000000) (848617113 / 500000000) (665151 / 125000) (83313 / 15625) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (527 / 2000) (529 / 2000) (665151 / 125000) (83313 / 15625) (20317 / 250) (20449 / 250)
    (54034 / 125) (88653 / 200) (549059 / 1000) (9097 / 1000000) (12932753 / 1000) (5977 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (665151 / 125000) (856640035527 / 100000) (5977 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (665151 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (665151 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell091 :
    ∀ t ∈ Set.Icc ((529 / 2000) : ℝ) (531 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((67889369 / 40000000) : ℝ) ≤ Real.exp (2 * (529 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (529 / 2000)) (67889369 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((531 / 2000) : ℝ)) ≤ (1700632091 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (531 / 2000)) (1700632091 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4422257475829 / 500000) : ℝ) ≤ Real.exp (3 * (5331861 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5331861 / 1000000)) (4422257475829 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((529 / 2000) : ℝ) (531 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5331861 / 1000000) (2671353 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (529 / 2000) (531 / 2000) (67889369 / 40000000) (1700632091 / 1000000000) (5331861 / 1000000) (2671353 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (529 / 2000) (531 / 2000) (5331861 / 1000000) (2671353 / 500000) (40829 / 500) (82187 / 1000)
    (436267 / 1000) (223659 / 500) (22791 / 40) (277 / 31250) (13036623 / 1000) (5789 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5331861 / 1000000) (4422257475829 / 500000) (5789 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5331861 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5331861 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell092 :
    ∀ t ∈ Set.Icc ((531 / 2000) : ℝ) (533 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((170063209 / 100000000) : ℝ) ≤ Real.exp (2 * (531 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (531 / 2000)) (170063209 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((533 / 2000) : ℝ)) ≤ (1704036759 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (533 / 2000)) (1704036759 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1141528918689 / 125000) : ℝ) ≤ Real.exp (3 * (1068507 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1068507 / 200000)) (1141528918689 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((531 / 2000) : ℝ) (533 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1068507 / 200000) (2676701 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (531 / 2000) (533 / 2000) (170063209 / 100000000) (1704036759 / 1000000000) (1068507 / 200000) (2676701 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (531 / 2000) (533 / 2000) (1068507 / 200000) (2676701 / 500000) (1641 / 20) (82581 / 1000)
    (110073 / 250) (451403 / 1000) (590799 / 1000) (8637 / 1000000) (13141333 / 1000) (28033 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1068507 / 200000) (1141528918689 / 125000) (28033 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1068507 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1068507 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell093 :
    ∀ t ∈ Set.Icc ((533 / 2000) : ℝ) (107 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((852018379 / 500000000) : ℝ) ≤ Real.exp (2 * (533 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (533 / 2000)) (852018379 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((107 / 400) : ℝ)) ≤ (1707448243 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (107 / 400)) (1707448243 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((589370422879 / 62500) : ℝ) ≤ Real.exp (3 * (5353231 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5353231 / 1000000)) (589370422879 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((533 / 2000) : ℝ) (107 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5353231 / 1000000) (134103 / 25000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (533 / 2000) (107 / 400) (852018379 / 500000000) (1707448243 / 1000000000) (5353231 / 1000000) (134103 / 25000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (533 / 2000) (107 / 400) (5353231 / 1000000) (134103 / 25000) (82443 / 1000) (10372 / 125)
    (111087 / 250) (227759 / 500) (4897 / 8) (4207 / 500000) (1324689 / 100) (6787 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5353231 / 1000000) (589370422879 / 62500) (6787 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5353231 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5353231 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell094 :
    ∀ t ∈ Set.Icc ((107 / 400) : ℝ) (537 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((853724121 / 500000000) : ℝ) ≤ Real.exp (2 * (107 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (107 / 400)) (853724121 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((537 / 2000) : ℝ)) ≤ (427716639 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (537 / 2000)) (427716639 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4868968478711 / 500000) : ℝ) ≤ Real.exp (3 * (1340987 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1340987 / 250000)) (4868968478711 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((107 / 400) : ℝ) (537 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1340987 / 250000) (5374859 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (107 / 400) (537 / 2000) (853724121 / 500000000) (427716639 / 250000000) (1340987 / 250000) (5374859 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (107 / 400) (537 / 2000) (1340987 / 250000) (5374859 / 1000000) (41419 / 500) (83373 / 1000)
    (89687 / 200) (57458 / 125) (633753 / 1000) (8197 / 1000000) (13353291 / 1000) (26289 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1340987 / 250000) (4868968478711 / 500000) (26289 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1340987 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1340987 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell095 :
    ∀ t ∈ Set.Icc ((537 / 2000) : ℝ) (539 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((342173311 / 200000000) : ℝ) ≤ Real.exp (2 * (537 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (537 / 2000)) (342173311 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((539 / 2000) : ℝ)) ≤ (857145857 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (539 / 2000)) (857145857 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((10056668147537 / 1000000) : ℝ) ≤ Real.exp (3 * (5374687 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5374687 / 1000000)) (10056668147537 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((537 / 2000) : ℝ) (539 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5374687 / 1000000) (5385619 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (537 / 2000) (539 / 2000) (342173311 / 200000000) (857145857 / 500000000) (5374687 / 1000000) (5385619 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (537 / 2000) (539 / 2000) (5374687 / 1000000) (5385619 / 1000000) (16647 / 200) (20943 / 250)
    (452553 / 1000) (463841 / 1000) (655679 / 1000) (1597 / 200000) (13460541 / 1000) (1591 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5374687 / 1000000) (10056668147537 / 1000000) (1591 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5374687 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5374687 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell096 :
    ∀ t ∈ Set.Icc ((539 / 2000) : ℝ) (541 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1714291713 / 1000000000) : ℝ) ≤ Real.exp (2 * (539 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (539 / 2000)) (1714291713 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((541 / 2000) : ℝ)) ≤ (107357733 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (541 / 2000)) (107357733 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((5193241272317 / 500000) : ℝ) ≤ Real.exp (3 * (5385447 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5385447 / 1000000)) (5193241272317 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((539 / 2000) : ℝ) (541 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5385447 / 1000000) (5396401 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (539 / 2000) (541 / 2000) (1714291713 / 1000000000) (107357733 / 62500000) (5385447 / 1000000) (5396401 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (539 / 2000) (541 / 2000) (5385447 / 1000000) (5396401 / 1000000) (83633 / 1000) (21043 / 250)
    (228351 / 500) (9361 / 20) (338963 / 500) (3889 / 500000) (13568657 / 1000) (3081 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5385447 / 1000000) (5193241272317 / 500000) (3081 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5385447 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5385447 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell097 :
    ∀ t ∈ Set.Icc ((541 / 2000) : ℝ) (543 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1717723727 / 1000000000) : ℝ) ≤ Real.exp (2 * (541 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (541 / 2000)) (1717723727 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((543 / 2000) : ℝ)) ≤ (1721162613 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (543 / 2000)) (1721162613 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((5363908854637 / 500000) : ℝ) ≤ Real.exp (3 * (5396229 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5396229 / 1000000)) (5363908854637 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((541 / 2000) : ℝ) (543 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5396229 / 1000000) (1081441 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (541 / 2000) (543 / 2000) (1717723727 / 1000000000) (1721162613 / 1000000000) (5396229 / 1000000) (1081441 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (541 / 2000) (543 / 2000) (5396229 / 1000000) (1081441 / 200000) (84033 / 1000) (3383 / 40)
    (230441 / 500) (472291 / 1000) (87561 / 125) (947 / 125000) (2735529 / 200) (2983 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5396229 / 1000000) (5363908854637 / 500000) (2983 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5396229 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5396229 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell098 :
    ∀ t ∈ Set.Icc ((543 / 2000) : ℝ) (109 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((430290653 / 250000000) : ℝ) ≤ Real.exp (2 * (543 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (543 / 2000)) (430290653 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((109 / 400) : ℝ)) ≤ (1724608383 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (109 / 400)) (1724608383 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((11081064465341 / 1000000) : ℝ) ≤ Real.exp (3 * (675879 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (675879 / 125000)) (11081064465341 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((543 / 2000) : ℝ) (109 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (675879 / 125000) (541803 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (543 / 2000) (109 / 400) (430290653 / 250000000) (1724608383 / 1000000000) (675879 / 125000) (541803 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (543 / 2000) (109 / 400) (675879 / 125000) (541803 / 100000) (16887 / 200) (84979 / 1000)
    (465093 / 1000) (476563 / 1000) (723367 / 1000) (7379 / 1000000) (13787503 / 1000) (23103 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (675879 / 125000) (11081064465341 / 1000000) (23103 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (675879 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (675879 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell099 :
    ∀ t ∈ Set.Icc ((109 / 400) : ℝ) (547 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((862304191 / 500000000) : ℝ) ≤ Real.exp (2 * (109 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (109 / 400)) (862304191 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((547 / 2000) : ℝ)) ≤ (1728061051 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (547 / 2000)) (1728061051 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1144669423429 / 100000) : ℝ) ≤ Real.exp (3 * (5417857 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5417857 / 1000000)) (1144669423429 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((109 / 400) : ℝ) (547 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5417857 / 1000000) (5428877 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (109 / 400) (547 / 2000) (862304191 / 500000000) (1728061051 / 1000000000) (5417857 / 1000000) (5428877 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (109 / 400) (547 / 2000) (5417857 / 1000000) (5428877 / 1000000) (84839 / 1000) (10673 / 125)
    (469337 / 1000) (120217 / 250) (746567 / 1000) (3593 / 500000) (6949123 / 500) (4473 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5417857 / 1000000) (1144669423429 / 100000) (4473 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5417857 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5417857 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityUpperExpCompact_cellsBatch004 :
    ∀ t ∈ Set.Icc ((507 / 2000) : ℝ) (547 / 2000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell080
      hpThetaDensityUpperExpCompact_cell081)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell082
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell083
      hpThetaDensityUpperExpCompact_cell084)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell085
      hpThetaDensityUpperExpCompact_cell086)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell087
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell088
      hpThetaDensityUpperExpCompact_cell089))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell090
      hpThetaDensityUpperExpCompact_cell091)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell092
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell093
      hpThetaDensityUpperExpCompact_cell094)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell095
      hpThetaDensityUpperExpCompact_cell096)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell097
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell098
      hpThetaDensityUpperExpCompact_cell099)))))

#print axioms hpThetaDensityUpperExpCompact_cellsBatch004
end HodgeProofHP
