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
theorem hpThetaDensityUpperExpCompact_cell240 :
    ∀ t ∈ Set.Icc ((827 / 2000) : ℝ) (829 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2286449093 / 1000000000) : ℝ) ≤ Real.exp (2 * (827 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (827 / 2000)) (2286449093 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((829 / 2000) : ℝ)) ≤ (286378321 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (829 / 2000)) (286378321 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((558823238501161 / 250000) : ℝ) ≤ Real.exp (3 * (7182879 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (7182879 / 1000000)) (558823238501161 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((827 / 2000) : ℝ) (829 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (7182879 / 1000000) (719749 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (827 / 2000) (829 / 2000) (2286449093 / 1000000000) (286378321 / 125000000) (7182879 / 1000000) (719749 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (827 / 2000) (829 / 2000) (7182879 / 1000000) (719749 / 100000) (16319 / 100) (164119 / 1000)
    (37959 / 25) (1543013 / 1000) (1942051 / 200) (87 / 1000000) (42938243 / 1000) (23 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (7182879 / 1000000) (558823238501161 / 250000) (23 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7182879 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7182879 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell241 :
    ∀ t ∈ Set.Icc ((829 / 2000) : ℝ) (831 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2291026567 / 1000000000) : ℝ) ≤ Real.exp (2 * (829 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (829 / 2000)) (2291026567 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((831 / 2000) : ℝ)) ≤ (2295613207 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (831 / 2000)) (2295613207 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1166317512499243 / 500000) : ℝ) ≤ Real.exp (3 * (7197259 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (7197259 / 1000000)) (1166317512499243 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((829 / 2000) : ℝ) (831 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (7197259 / 1000000) (7211899 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (829 / 2000) (831 / 2000) (2291026567 / 1000000000) (2295613207 / 1000000000) (7197259 / 1000000) (7211899 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (829 / 2000) (831 / 2000) (7197259 / 1000000) (7211899 / 1000000) (16393 / 100) (164863 / 1000)
    (1530189 / 1000) (194372 / 125) (1967813 / 200) (83 / 1000000) (43283117 / 1000) (11 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (7197259 / 1000000) (1166317512499243 / 500000) (11 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7197259 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7197259 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell242 :
    ∀ t ∈ Set.Icc ((831 / 2000) : ℝ) (833 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((459122641 / 200000000) : ℝ) ≤ Real.exp (2 * (831 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (831 / 2000)) (459122641 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((833 / 2000) : ℝ)) ≤ (2300209027 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (833 / 2000)) (2300209027 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((243440092459307 / 100000) : ℝ) ≤ Real.exp (3 * (1802917 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1802917 / 250000)) (243440092459307 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((831 / 2000) : ℝ) (833 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1802917 / 250000) (7226337 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (831 / 2000) (833 / 2000) (459122641 / 200000000) (2300209027 / 1000000000) (1802917 / 250000) (7226337 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (831 / 2000) (833 / 2000) (1802917 / 250000) (7226337 / 1000000) (82337 / 500) (16561 / 100)
    (1542101 / 1000) (783511 / 500) (9969277 / 1000) (81 / 1000000) (8726153 / 200) (53 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1802917 / 250000) (243440092459307 / 100000) (53 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1802917 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1802917 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell243 :
    ∀ t ∈ Set.Icc ((833 / 2000) : ℝ) (167 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1150104513 / 500000000) : ℝ) ≤ Real.exp (2 * (833 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (833 / 2000)) (1150104513 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((167 / 400) : ℝ)) ≤ (2304814049 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (167 / 400)) (2304814049 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((317599867434171 / 125000) : ℝ) ≤ Real.exp (3 * (3613053 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3613053 / 500000)) (317599867434171 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((833 / 2000) : ℝ) (167 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3613053 / 500000) (1810201 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (833 / 2000) (167 / 400) (1150104513 / 500000000) (2304814049 / 1000000000) (3613053 / 500000) (1810201 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (833 / 2000) (167 / 400) (3613053 / 500000) (1810201 / 250000) (165421 / 1000) (166361 / 1000)
    (194262 / 125) (1579153 / 1000) (10100907 / 1000) (77 / 1000000) (5497651 / 125) (101 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3613053 / 500000) (317599867434171 / 125000) (101 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3613053 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3613053 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell244 :
    ∀ t ∈ Set.Icc ((167 / 400) : ℝ) (837 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((72025439 / 31250000) : ℝ) ≤ Real.exp (2 * (167 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (167 / 400)) (72025439 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((837 / 2000) : ℝ)) ≤ (230942829 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (837 / 2000)) (230942829 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((530409491497257 / 200000) : ℝ) ≤ Real.exp (3 * (7240573 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (7240573 / 1000000)) (530409491497257 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((167 / 400) : ℝ) (837 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (7240573 / 1000000) (72553 / 10000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (167 / 400) (837 / 2000) (72025439 / 31250000) (230942829 / 100000000) (7240573 / 1000000) (72553 / 10000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (167 / 400) (837 / 2000) (7240573 / 1000000) (72553 / 10000) (166171 / 1000) (33423 / 200)
    (62647 / 40) (1591369 / 1000) (5116983 / 500) (3 / 40000) (44334467 / 1000) (97 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (7240573 / 1000000) (530409491497257 / 200000) (97 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7240573 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7240573 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell245 :
    ∀ t ∈ Set.Icc ((837 / 2000) : ℝ) (839 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((36084817 / 15625000) : ℝ) ≤ Real.exp (2 * (837 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (837 / 2000)) (36084817 / 15625000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((839 / 2000) : ℝ)) ≤ (289256471 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (839 / 2000)) (289256471 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1384183636244057 / 500000) : ℝ) ≤ Real.exp (3 * (1813767 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1813767 / 250000)) (1384183636244057 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((837 / 2000) : ℝ) (839 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1813767 / 250000) (3634913 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (837 / 2000) (839 / 2000) (36084817 / 15625000) (289256471 / 125000000) (1813767 / 250000) (3634913 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (837 / 2000) (839 / 2000) (1813767 / 250000) (3634913 / 500000) (6677 / 40) (20984 / 125)
    (1578337 / 1000) (1603671 / 1000) (5184257 / 500) (9 / 125000) (22345293 / 500) (93 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1813767 / 250000) (1384183636244057 / 500000) (93 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1813767 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1813767 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell246 :
    ∀ t ∈ Set.Icc ((839 / 2000) : ℝ) (841 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2314051767 / 1000000000) : ℝ) ≤ Real.exp (2 * (839 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (839 / 2000)) (2314051767 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((841 / 2000) : ℝ)) ≤ (2318684503 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (841 / 2000)) (2318684503 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2890014543038689 / 1000000) : ℝ) ≤ Real.exp (3 * (7269593 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (7269593 / 1000000)) (2890014543038689 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((839 / 2000) : ℝ) (841 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (7269593 / 1000000) (364219 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (839 / 2000) (841 / 2000) (2314051767 / 1000000000) (2318684503 / 1000000000) (7269593 / 1000000) (364219 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (839 / 2000) (841 / 2000) (7269593 / 1000000) (364219 / 50000) (167681 / 1000) (21079 / 125)
    (795293 / 500) (808029 / 500) (5252237 / 500) (7 / 100000) (2252477 / 50) (89 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (7269593 / 1000000) (2890014543038689 / 1000000) (89 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7269593 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7269593 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell247 :
    ∀ t ∈ Set.Icc ((841 / 2000) : ℝ) (843 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1159342251 / 500000000) : ℝ) ≤ Real.exp (2 * (841 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (841 / 2000)) (1159342251 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((843 / 2000) : ℝ)) ≤ (145207907 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (843 / 2000)) (145207907 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((94288538155279 / 31250) : ℝ) ≤ Real.exp (3 * (7284147 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (7284147 / 1000000)) (94288538155279 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((841 / 2000) : ℝ) (843 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (7284147 / 1000000) (7298963 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (841 / 2000) (843 / 2000) (1159342251 / 500000000) (145207907 / 62500000) (7284147 / 1000000) (7298963 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (841 / 2000) (843 / 2000) (7284147 / 1000000) (7298963 / 1000000) (168441 / 1000) (33879 / 200)
    (1602921 / 1000) (1628531 / 1000) (2128381 / 200) (67 / 1000000) (45411373 / 1000) (17 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (7284147 / 1000000) (94288538155279 / 31250) (17 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7284147 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7284147 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell248 :
    ∀ t ∈ Set.Icc ((843 / 2000) : ℝ) (169 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2323326511 / 1000000000) : ℝ) ≤ Real.exp (2 * (843 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (843 / 2000)) (2323326511 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((169 / 400) : ℝ)) ≤ (465595563 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (169 / 400)) (465595563 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1575143690368379 / 500000) : ℝ) ≤ Real.exp (3 * (729873 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (729873 / 100000)) (1575143690368379 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((843 / 2000) : ℝ) (169 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (729873 / 100000) (914197 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (843 / 2000) (169 / 400) (2323326511 / 1000000000) (465595563 / 200000000) (729873 / 100000) (914197 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (843 / 2000) (169 / 400) (729873 / 100000) (914197 / 125000) (42301 / 250) (85081 / 500)
    (1615341 / 1000) (410273 / 250) (1347606 / 125) (13 / 200000) (45776133 / 1000) (41 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (729873 / 100000) (1575143690368379 / 500000) (41 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (729873 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (729873 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell249 :
    ∀ t ∈ Set.Icc ((169 / 400) : ℝ) (847 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1163988907 / 500000000) : ℝ) ≤ Real.exp (2 * (169 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (169 / 400)) (1163988907 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((847 / 2000) : ℝ)) ≤ (233263843 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (847 / 2000)) (233263843 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((164472698842709 / 50000) : ℝ) ≤ Real.exp (3 * (3656671 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3656671 / 500000)) (164472698842709 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((169 / 400) : ℝ) (847 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3656671 / 500000) (7328217 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (169 / 400) (847 / 2000) (1163988907 / 500000000) (233263843 / 100000000) (3656671 / 500000) (7328217 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (169 / 400) (847 / 2000) (3656671 / 500000) (7328217 / 1000000) (16997 / 100) (42733 / 250)
    (203481 / 125) (1653739 / 1000) (10921261 / 1000) (31 / 500000) (46143791 / 1000) (39 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3656671 / 500000) (164472698842709 / 50000) (39 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3656671 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3656671 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell250 :
    ∀ t ∈ Set.Icc ((847 / 2000) : ℝ) (849 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((583159607 / 250000000) : ℝ) ≤ Real.exp (2 * (847 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (847 / 2000)) (583159607 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((849 / 2000) : ℝ)) ≤ (18698467 / 8000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (849 / 2000)) (18698467 / 8000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3435023487260617 / 1000000) : ℝ) ≤ Real.exp (3 * (7327983 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (7327983 / 1000000)) (3435023487260617 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((847 / 2000) : ℝ) (849 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (7327983 / 1000000) (917861 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (847 / 2000) (849 / 2000) (583159607 / 250000000) (18698467 / 8000000) (7327983 / 1000000) (917861 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (847 / 2000) (849 / 2000) (7327983 / 1000000) (917861 / 125000) (8537 / 50) (34341 / 200)
    (820221 / 500) (66659 / 40) (1382902 / 125) (3 / 50000) (46514419 / 1000) (3 / 40000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (7327983 / 1000000) (3435023487260617 / 1000000) (3 / 40000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7327983 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7327983 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell251 :
    ∀ t ∈ Set.Icc ((849 / 2000) : ℝ) (851 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1168654187 / 500000000) : ℝ) ≤ Real.exp (2 * (849 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (849 / 2000)) (1168654187 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((851 / 2000) : ℝ)) ≤ (2341987669 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (851 / 2000)) (2341987669 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((28698489559737 / 8000) : ℝ) ≤ Real.exp (3 * (3671327 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3671327 / 500000)) (28698489559737 / 8000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((849 / 2000) : ℝ) (851 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3671327 / 500000) (7357589 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (849 / 2000) (851 / 2000) (1168654187 / 500000000) (2341987669 / 1000000000) (3671327 / 500000) (7357589 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (849 / 2000) (851 / 2000) (3671327 / 500000) (7357589 / 1000000) (21439 / 125) (172481 / 1000)
    (413281 / 250) (16793 / 10) (5603353 / 500) (29 / 500000) (46888041 / 1000) (9 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3671327 / 500000) (28698489559737 / 8000) (9 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3671327 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3671327 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell252 :
    ∀ t ∈ Set.Icc ((851 / 2000) : ℝ) (853 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((585496917 / 250000000) : ℝ) ≤ Real.exp (2 * (851 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (851 / 2000)) (585496917 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((853 / 2000) : ℝ)) ≤ (586669083 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (853 / 2000)) (586669083 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3746627018048817 / 1000000) : ℝ) ≤ Real.exp (3 * (3678677 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3678677 / 500000)) (3746627018048817 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((851 / 2000) : ℝ) (853 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3678677 / 500000) (7372319 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (851 / 2000) (853 / 2000) (585496917 / 250000000) (586669083 / 250000000) (3678677 / 500000) (7372319 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (851 / 2000) (853 / 2000) (3678677 / 500000) (7372319 / 1000000) (21536 / 125) (173261 / 1000)
    (832947 / 500) (846107 / 500) (5675869 / 500) (7 / 125000) (11816163 / 250) (69 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3678677 / 500000) (3746627018048817 / 1000000) (69 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3678677 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3678677 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell253 :
    ∀ t ∈ Set.Icc ((853 / 2000) : ℝ) (171 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2346676331 / 1000000000) : ℝ) ≤ Real.exp (2 * (853 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (853 / 2000)) (2346676331 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((171 / 400) : ℝ)) ≤ (2351374381 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (171 / 400)) (2351374381 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3913306265656783 / 1000000) : ℝ) ≤ Real.exp (3 * (7372083 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (7372083 / 1000000)) (3913306265656783 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((853 / 2000) : ℝ) (171 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (7372083 / 1000000) (3693539 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (853 / 2000) (171 / 400) (2346676331 / 1000000000) (2351374381 / 1000000000) (7372083 / 1000000) (3693539 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (853 / 2000) (171 / 400) (7372083 / 1000000) (3693539 / 500000) (173067 / 1000) (43511 / 250)
    (839377 / 500) (1705217 / 1000) (5749163 / 500) (27 / 500000) (1905771 / 40) (33 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (7372083 / 1000000) (3913306265656783 / 1000000) (33 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7372083 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7372083 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell254 :
    ∀ t ∈ Set.Icc ((171 / 400) : ℝ) (857 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((117568719 / 50000000) : ℝ) ≤ Real.exp (2 * (171 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (171 / 400)) (117568719 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((857 / 2000) : ℝ)) ≤ (589020459 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (857 / 2000)) (589020459 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2043856383913697 / 500000) : ℝ) ≤ Real.exp (3 * (3693421 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3693421 / 500000)) (2043856383913697 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((171 / 400) : ℝ) (857 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3693421 / 500000) (7401867 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (171 / 400) (857 / 2000) (117568719 / 50000000) (589020459 / 250000000) (3693421 / 500000) (7401867 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (171 / 400) (857 / 2000) (3693421 / 500000) (7401867 / 1000000) (3477 / 20) (17483 / 100)
    (1691703 / 1000) (214789 / 125) (5823247 / 500) (13 / 250000) (1200674 / 25) (63 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3693421 / 500000) (2043856383913697 / 500000) (63 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693421 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3693421 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell255 :
    ∀ t ∈ Set.Icc ((857 / 2000) : ℝ) (859 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1178040917 / 500000000) : ℝ) ≤ Real.exp (2 * (857 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (857 / 2000)) (1178040917 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((859 / 2000) : ℝ)) ≤ (472159743 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (859 / 2000)) (472159743 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2135108578850451 / 500000) : ℝ) ≤ Real.exp (3 * (7401631 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (7401631 / 1000000)) (2135108578850451 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((857 / 2000) : ℝ) (859 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (7401631 / 1000000) (3708343 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (857 / 2000) (859 / 2000) (1178040917 / 500000000) (472159743 / 200000000) (7401631 / 1000000) (3708343 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (857 / 2000) (859 / 2000) (7401631 / 1000000) (3708343 / 500000) (43659 / 250) (8781 / 50)
    (1704743 / 1000) (1731497 / 1000) (1474532 / 125) (1 / 20000) (6051591 / 125) (3 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (7401631 / 1000000) (2135108578850451 / 500000) (3 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7401631 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7401631 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell256 :
    ∀ t ∈ Set.Icc ((859 / 2000) : ℝ) (861 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2360798713 / 1000000000) : ℝ) ≤ Real.exp (2 * (859 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (859 / 2000)) (2360798713 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((861 / 2000) : ℝ)) ≤ (2365525037 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (861 / 2000)) (2365525037 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4461195185235963 / 1000000) : ℝ) ≤ Real.exp (3 * (7416449 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (7416449 / 1000000)) (4461195185235963 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((859 / 2000) : ℝ) (861 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (7416449 / 1000000) (3715767 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (859 / 2000) (861 / 2000) (2360798713 / 1000000000) (2365525037 / 1000000000) (7416449 / 1000000) (3715767 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (859 / 2000) (861 / 2000) (7416449 / 1000000) (3715767 / 500000) (7017 / 40) (176413 / 1000)
    (1717873 / 1000) (872387 / 500) (11947619 / 1000) (3 / 62500) (24400789 / 500) (29 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (7416449 / 1000000) (4461195185235963 / 1000000) (29 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7416449 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7416449 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell257 :
    ∀ t ∈ Set.Icc ((861 / 2000) : ℝ) (863 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((591381259 / 250000000) : ℝ) ≤ Real.exp (2 * (861 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (861 / 2000)) (591381259 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((863 / 2000) : ℝ)) ≤ (2370260821 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (863 / 2000)) (2370260821 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4661053223680089 / 1000000) : ℝ) ≤ Real.exp (3 * (116114 / 15625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (116114 / 15625)) (4661053223680089 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((861 / 2000) : ℝ) (863 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (116114 / 15625) (1861603 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (861 / 2000) (863 / 2000) (591381259 / 250000000) (2370260821 / 1000000000) (116114 / 15625) (1861603 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (861 / 2000) (863 / 2000) (116114 / 15625) (1861603 / 250000) (88109 / 500) (177209 / 1000)
    (865547 / 500) (219768 / 125) (96805 / 8) (23 / 500000) (24596779 / 500) (11 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (116114 / 15625) (4661053223680089 / 1000000) (11 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (116114 / 15625)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (116114 / 15625)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell258 :
    ∀ t ∈ Set.Icc ((863 / 2000) : ℝ) (173 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((118513041 / 50000000) : ℝ) ≤ Real.exp (2 * (863 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (863 / 2000)) (118513041 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((173 / 400) : ℝ)) ≤ (1187503043 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (173 / 400)) (1187503043 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1217561601141967 / 250000) : ℝ) ≤ Real.exp (3 * (3723087 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3723087 / 500000)) (1217561601141967 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((863 / 2000) : ℝ) (173 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3723087 / 500000) (186533 / 25000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (863 / 2000) (173 / 400) (118513041 / 50000000) (1187503043 / 500000000) (3723087 / 500000) (186533 / 25000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (863 / 2000) (173 / 400) (3723087 / 500000) (186533 / 25000) (88507 / 500) (178009 / 1000)
    (218051 / 125) (885803 / 500) (3063813 / 250) (9 / 200000) (12397173 / 250) (53 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3723087 / 500000) (1217561601141967 / 250000) (53 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3723087 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3723087 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell259 :
    ∀ t ∈ Set.Icc ((173 / 400) : ℝ) (867 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((475001217 / 200000000) : ℝ) ≤ Real.exp (2 * (173 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (173 / 400)) (475001217 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((867 / 2000) : ℝ)) ≤ (594940213 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (867 / 2000)) (594940213 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((5089195976011343 / 1000000) : ℝ) ≤ Real.exp (3 * (7461081 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (7461081 / 1000000)) (5089195976011343 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((173 / 400) : ℝ) (867 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (7461081 / 1000000) (7476257 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (173 / 400) (867 / 2000) (475001217 / 200000000) (594940213 / 250000000) (7461081 / 1000000) (7476257 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (173 / 400) (867 / 2000) (7461081 / 1000000) (7476257 / 1000000) (177813 / 1000) (44703 / 250)
    (351563 / 200) (1785161 / 1000) (3102881 / 250) (43 / 1000000) (49986977 / 1000) (51 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (7461081 / 1000000) (5089195976011343 / 1000000) (51 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7461081 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7461081 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityUpperExpCompact_cellsBatch012 :
    ∀ t ∈ Set.Icc ((827 / 2000) : ℝ) (867 / 2000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell240
      hpThetaDensityUpperExpCompact_cell241)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell242
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell243
      hpThetaDensityUpperExpCompact_cell244)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell245
      hpThetaDensityUpperExpCompact_cell246)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell247
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell248
      hpThetaDensityUpperExpCompact_cell249))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell250
      hpThetaDensityUpperExpCompact_cell251)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell252
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell253
      hpThetaDensityUpperExpCompact_cell254)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell255
      hpThetaDensityUpperExpCompact_cell256)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell257
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell258
      hpThetaDensityUpperExpCompact_cell259)))))

#print axioms hpThetaDensityUpperExpCompact_cellsBatch012
end HodgeProofHP
