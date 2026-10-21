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
theorem hpThetaDensityUpperExpCompact_cell020 :
    ∀ t ∈ Set.Icc ((21 / 100) : ℝ) (421 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((304392311 / 200000000) : ℝ) ≤ Real.exp (2 * (21 / 100)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (21 / 100)) (304392311 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((421 / 2000) : ℝ)) ≤ (1523484279 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (421 / 2000)) (1523484279 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((105989683831 / 62500) : ℝ) ≤ Real.exp (3 * (2390621 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2390621 / 500000)) (105989683831 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((21 / 100) : ℝ) (421 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2390621 / 500000) (4786179 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (21 / 100) (421 / 2000) (304392311 / 200000000) (1523484279 / 1000000000) (2390621 / 500000) (4786179 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (21 / 100) (421 / 2000) (2390621 / 500000) (4786179 / 1000000) (15681 / 250) (62943 / 1000)
    (258897 / 1000) (2631 / 10) (-4903 / 20) (6647 / 200000) (1049508 / 125) (150959 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2390621 / 500000) (105989683831 / 62500) (150959 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2390621 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2390621 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell021 :
    ∀ t ∈ Set.Icc ((421 / 2000) : ℝ) (211 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((761742139 / 500000000) : ℝ) ≤ Real.exp (2 * (421 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (421 / 2000)) (761742139 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((211 / 1000) : ℝ)) ≤ (61000341 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (211 / 1000)) (61000341 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1720342613 / 1000) : ℝ) ≤ Real.exp (3 * (191441 / 40000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (191441 / 40000)) (1720342613 / 1000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((421 / 2000) : ℝ) (211 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (191441 / 40000) (4790967 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (421 / 2000) (211 / 1000) (761742139 / 500000000) (61000341 / 40000000) (191441 / 40000) (4790967 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (421 / 2000) (211 / 1000) (191441 / 40000) (4790967 / 1000000) (31439 / 500) (31549 / 500)
    (13011 / 50) (132217 / 500) (-240891 / 1000) (1643 / 50000) (1053714 / 125) (18601 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (191441 / 40000) (1720342613 / 1000) (18601 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (191441 / 40000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (191441 / 40000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell022 :
    ∀ t ∈ Set.Icc ((211 / 1000) : ℝ) (423 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((381252131 / 250000000) : ℝ) ≤ Real.exp (2 * (211 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (211 / 1000)) (381252131 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((423 / 2000) : ℝ)) ≤ (190816787 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (423 / 2000)) (190816787 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1745235852309 / 1000000) : ℝ) ≤ Real.exp (3 * (2395407 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2395407 / 500000)) (1745235852309 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((211 / 1000) : ℝ) (423 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2395407 / 500000) (4795761 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (211 / 1000) (423 / 2000) (381252131 / 250000000) (190816787 / 125000000) (2395407 / 500000) (4795761 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (211 / 1000) (423 / 2000) (2395407 / 500000) (4795761 / 1000000) (63033 / 1000) (63253 / 1000)
    (65387 / 250) (132887 / 500) (-29574 / 125) (32489 / 1000000) (8463503 / 1000) (73343 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2395407 / 500000) (1745235852309 / 1000000) (73343 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2395407 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2395407 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell023 :
    ∀ t ∈ Set.Icc ((423 / 2000) : ℝ) (53 / 250), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((305306859 / 200000000) : ℝ) ≤ Real.exp (2 * (423 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (423 / 2000)) (305306859 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((53 / 250) : ℝ)) ≤ (764030797 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (53 / 250)) (764030797 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1770510517399 / 1000000) : ℝ) ≤ Real.exp (3 * (4795607 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4795607 / 1000000)) (1770510517399 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((423 / 2000) : ℝ) (53 / 250),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4795607 / 1000000) (4800559 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (423 / 2000) (53 / 250) (305306859 / 200000000) (764030797 / 500000000) (4795607 / 1000000) (4800559 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (423 / 2000) (53 / 250) (4795607 / 1000000) (4800559 / 1000000) (15797 / 250) (7926 / 125)
    (131441 / 500) (267119 / 1000) (-232253 / 1000) (32121 / 1000000) (8497423 / 1000) (9037 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4795607 / 1000000) (1770510517399 / 1000000) (9037 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4795607 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4795607 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell024 :
    ∀ t ∈ Set.Icc ((53 / 250) : ℝ) (17 / 80), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1528061593 / 1000000000) : ℝ) ≤ Real.exp (2 * (53 / 250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (53 / 250)) (1528061593 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((17 / 80) : ℝ)) ≤ (76479521 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (17 / 80)) (76479521 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1796178130251 / 1000000) : ℝ) ≤ Real.exp (3 * (960081 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (960081 / 200000)) (1796178130251 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((53 / 250) : ℝ) (17 / 80),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (960081 / 200000) (2402681 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (53 / 250) (17 / 80) (1528061593 / 1000000000) (76479521 / 50000000) (960081 / 200000) (2402681 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (53 / 250) (17 / 80) (960081 / 200000) (2402681 / 500000) (63343 / 1000) (15891 / 250)
    (13211 / 50) (268469 / 1000) (-1823 / 8) (31757 / 1000000) (8531481 / 1000) (5701 / 40000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (960081 / 200000) (1796178130251 / 1000000) (5701 / 40000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (960081 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (960081 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell025 :
    ∀ t ∈ Set.Icc ((17 / 80) : ℝ) (213 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1529590419 / 1000000000) : ℝ) ≤ Real.exp (2 * (17 / 80)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (17 / 80)) (1529590419 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((213 / 1000) : ℝ)) ≤ (191390097 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (213 / 1000)) (191390097 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((227780645253 / 125000) : ℝ) ≤ Real.exp (3 * (600651 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (600651 / 125000)) (227780645253 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((17 / 80) : ℝ) (213 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (600651 / 125000) (481017 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (17 / 80) (213 / 1000) (1529590419 / 1000000000) (191390097 / 125000000) (600651 / 125000) (481017 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (17 / 80) (213 / 1000) (600651 / 125000) (481017 / 100000) (63499 / 1000) (1593 / 25)
    (66391 / 250) (33728 / 125) (-223457 / 1000) (31397 / 1000000) (8565677 / 1000) (140487 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (600651 / 125000) (227780645253 / 125000) (140487 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (600651 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (600651 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell026 :
    ∀ t ∈ Set.Icc ((213 / 1000) : ℝ) (427 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((61244831 / 40000000) : ℝ) ≤ Real.exp (2 * (213 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (213 / 1000)) (61244831 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((427 / 2000) : ℝ)) ≤ (766326331 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (427 / 2000)) (766326331 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((462178162493 / 250000) : ℝ) ≤ Real.exp (3 * (962003 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (962003 / 200000)) (462178162493 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((213 / 1000) : ℝ) (427 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (962003 / 200000) (2407491 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (213 / 1000) (427 / 2000) (61244831 / 40000000) (766326331 / 500000000) (962003 / 200000) (2407491 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (213 / 1000) (427 / 2000) (962003 / 200000) (2407491 / 500000) (12731 / 200) (63877 / 1000)
    (133457 / 500) (33898 / 125) (-218999 / 1000) (97 / 3125) (1720001 / 200) (5539 / 40000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (962003 / 200000) (462178162493 / 250000) (5539 / 40000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (962003 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (962003 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell027 :
    ∀ t ∈ Set.Icc ((427 / 2000) : ℝ) (107 / 500), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1532652661 / 1000000000) : ℝ) ≤ Real.exp (2 * (427 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (427 / 2000)) (1532652661 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((107 / 500) : ℝ)) ≤ (1534186081 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (107 / 500)) (1534186081 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1875598302141 / 1000000) : ℝ) ≤ Real.exp (3 * (1203707 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1203707 / 250000)) (1875598302141 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((427 / 2000) : ℝ) (107 / 500),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1203707 / 250000) (4819799 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (427 / 2000) (107 / 500) (1532652661 / 1000000000) (1534186081 / 1000000000) (1203707 / 250000) (4819799 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (427 / 2000) (107 / 500) (1203707 / 250000) (4819799 / 1000000) (63811 / 1000) (64033 / 1000)
    (268269 / 1000) (5451 / 20) (-53627 / 250) (30687 / 1000000) (8634471 / 1000) (13649 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1203707 / 250000) (1875598302141 / 1000000) (13649 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1203707 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1203707 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell028 :
    ∀ t ∈ Set.Icc ((107 / 500) : ℝ) (429 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((9588663 / 6250000) : ℝ) ≤ Real.exp (2 * (107 / 500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (107 / 500)) (9588663 / 6250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((429 / 2000) : ℝ)) ≤ (307144207 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (429 / 2000)) (307144207 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((951448878379 / 500000) : ℝ) ≤ Real.exp (3 * (963929 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (963929 / 200000)) (951448878379 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((107 / 500) : ℝ) (429 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (963929 / 200000) (2412311 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (107 / 500) (429 / 2000) (9588663 / 6250000) (307144207 / 200000000) (963929 / 200000) (2412311 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (107 / 500) (429 / 2000) (963929 / 200000) (2412311 / 500000) (7996 / 125) (64191 / 1000)
    (67407 / 250) (273921 / 1000) (-5249 / 25) (15169 / 500000) (8669083 / 1000) (33633 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (963929 / 200000) (951448878379 / 500000) (33633 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (963929 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (963929 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell029 :
    ∀ t ∈ Set.Icc ((429 / 2000) : ℝ) (43 / 200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((767860517 / 500000000) : ℝ) ≤ Real.exp (2 * (429 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (429 / 2000)) (767860517 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43 / 200) : ℝ)) ≤ (384314381 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43 / 200)) (384314381 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1930623486959 / 1000000) : ℝ) ≤ Real.exp (3 * (4824467 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4824467 / 1000000)) (1930623486959 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((429 / 2000) : ℝ) (43 / 200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4824467 / 1000000) (4829449 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (429 / 2000) (43 / 200) (767860517 / 500000000) (384314381 / 250000000) (4824467 / 1000000) (4829449 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (429 / 2000) (43 / 200) (4824467 / 1000000) (4829449 / 1000000) (513 / 8) (16087 / 250)
    (135497 / 500) (137649 / 500) (-205379 / 1000) (3749 / 125000) (8703829 / 1000) (663 / 5000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4824467 / 1000000) (1930623486959 / 1000000) (663 / 5000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4824467 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4824467 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell030 :
    ∀ t ∈ Set.Icc ((43 / 200) : ℝ) (431 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1537257523 / 1000000000) : ℝ) ≤ Real.exp (2 * (43 / 200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43 / 200)) (1537257523 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((431 / 2000) : ℝ)) ≤ (30775911 / 20000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (431 / 2000)) (30775911 / 20000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1958782540199 / 1000000) : ℝ) ≤ Real.exp (3 * (2414647 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2414647 / 500000)) (1958782540199 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43 / 200) : ℝ) (431 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2414647 / 500000) (4834281 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43 / 200) (431 / 2000) (1537257523 / 1000000000) (30775911 / 20000000) (2414647 / 500000) (4834281 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43 / 200) (431 / 2000) (2414647 / 500000) (4834281 / 1000000) (32141 / 500) (32253 / 500)
    (68091 / 250) (6917 / 25) (-200757 / 1000) (593 / 20000) (1747743 / 200) (65347 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2414647 / 500000) (1958782540199 / 1000000) (65347 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2414647 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2414647 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell031 :
    ∀ t ∈ Set.Icc ((431 / 2000) : ℝ) (27 / 125), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1538795549 / 1000000000) : ℝ) ≤ Real.exp (2 * (431 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (431 / 2000)) (1538795549 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((27 / 125) : ℝ)) ≤ (385083779 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (27 / 125)) (385083779 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1987382086267 / 1000000) : ℝ) ≤ Real.exp (3 * (2417063 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2417063 / 500000)) (1987382086267 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((431 / 2000) : ℝ) (27 / 125),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2417063 / 500000) (4839117 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (431 / 2000) (27 / 125) (1538795549 / 1000000000) (385083779 / 250000000) (2417063 / 500000) (4839117 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (431 / 2000) (27 / 125) (2417063 / 500000) (4839117 / 1000000) (1611 / 25) (8083 / 125)
    (273741 / 1000) (278067 / 1000) (-98051 / 500) (29311 / 1000000) (1754747 / 200) (128813 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2417063 / 500000) (1987382086267 / 1000000) (128813 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2417063 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2417063 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell032 :
    ∀ t ∈ Set.Icc ((27 / 125) : ℝ) (433 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((308067023 / 200000000) : ℝ) ≤ Real.exp (2 * (27 / 125)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (27 / 125)) (308067023 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((433 / 2000) : ℝ)) ≤ (1541876221 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (433 / 2000)) (1541876221 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((504105842649 / 250000) : ℝ) ≤ Real.exp (3 * (2419481 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2419481 / 500000)) (504105842649 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((27 / 125) : ℝ) (433 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2419481 / 500000) (4843959 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (27 / 125) (433 / 2000) (308067023 / 200000000) (1541876221 / 1000000000) (2419481 / 500000) (4843959 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (27 / 125) (433 / 2000) (2419481 / 500000) (4843959 / 1000000) (32299 / 500) (32411 / 500)
    (137561 / 500) (13973 / 50) (-191389 / 1000) (1811 / 62500) (8808903 / 1000) (63479 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2419481 / 500000) (504105842649 / 250000) (63479 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2419481 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2419481 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell033 :
    ∀ t ∈ Set.Icc ((433 / 2000) : ℝ) (217 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((77093811 / 50000000) : ℝ) ≤ Real.exp (2 * (433 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (433 / 2000)) (77093811 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((217 / 1000) : ℝ)) ≤ (1543418869 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (217 / 1000)) (1543418869 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16367406589 / 8000) : ℝ) ≤ Real.exp (3 * (1210951 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1210951 / 250000)) (16367406589 / 8000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((433 / 2000) : ℝ) (217 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1210951 / 250000) (969761 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (433 / 2000) (217 / 1000) (77093811 / 50000000) (1543418869 / 1000000000) (1210951 / 250000) (969761 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (433 / 2000) (217 / 1000) (1210951 / 250000) (969761 / 200000) (16189 / 250) (64981 / 1000)
    (276509 / 1000) (140429 / 500) (-3733 / 20) (7161 / 250000) (8844207 / 1000) (125127 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1210951 / 250000) (16367406589 / 8000) (125127 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1210951 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1210951 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell034 :
    ∀ t ∈ Set.Icc ((217 / 1000) : ℝ) (87 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((385854717 / 250000000) : ℝ) ≤ Real.exp (2 * (217 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (217 / 1000)) (385854717 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((87 / 400) : ℝ)) ≤ (1544963059 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (87 / 400)) (1544963059 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2075884806541 / 1000000) : ℝ) ≤ Real.exp (3 * (96973 / 20000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (96973 / 20000)) (2075884806541 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((217 / 1000) : ℝ) (87 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (96973 / 20000) (606707 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (217 / 1000) (87 / 400) (385854717 / 250000000) (1544963059 / 1000000000) (96973 / 20000) (606707 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (217 / 1000) (87 / 400) (96973 / 20000) (606707 / 125000) (12983 / 200) (65141 / 1000)
    (277901 / 1000) (141131 / 500) (-181861 / 1000) (5663 / 200000) (8879653 / 1000) (123321 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (96973 / 20000) (2075884806541 / 1000000) (123321 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (96973 / 20000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (96973 / 20000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell035 :
    ∀ t ∈ Set.Icc ((87 / 400) : ℝ) (109 / 500), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((772481529 / 500000000) : ℝ) ≤ Real.exp (2 * (87 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (87 / 400)) (772481529 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((109 / 500) : ℝ)) ≤ (309301759 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (109 / 500)) (309301759 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1053157022849 / 500000) : ℝ) ≤ Real.exp (3 * (4853501 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4853501 / 1000000)) (1053157022849 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((87 / 400) : ℝ) (109 / 500),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4853501 / 1000000) (4858513 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (87 / 400) (109 / 500) (772481529 / 500000000) (309301759 / 200000000) (4853501 / 1000000) (4858513 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (87 / 400) (109 / 500) (4853501 / 1000000) (4858513 / 1000000) (32537 / 500) (653 / 10)
    (139649 / 500) (283671 / 1000) (-8851 / 50) (2799 / 100000) (8915249 / 1000) (6077 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4853501 / 1000000) (1053157022849 / 500000) (6077 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4853501 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4853501 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell036 :
    ∀ t ∈ Set.Icc ((109 / 500) : ℝ) (437 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((773254397 / 500000000) : ℝ) ≤ Real.exp (2 * (109 / 500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (109 / 500)) (773254397 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((437 / 2000) : ℝ)) ≤ (774028039 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (437 / 2000)) (774028039 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2137221352289 / 1000000) : ℝ) ≤ Real.exp (3 * (4858357 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4858357 / 1000000)) (2137221352289 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((109 / 500) : ℝ) (437 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4858357 / 1000000) (4863373 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (109 / 500) (437 / 2000) (773254397 / 500000000) (774028039 / 500000000) (4858357 / 1000000) (4863373 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (109 / 500) (437 / 2000) (4858357 / 1000000) (4863373 / 1000000) (32617 / 500) (3273 / 50)
    (140351 / 500) (142543 / 500) (-86077 / 500) (6917 / 250000) (358039 / 40) (59891 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4858357 / 1000000) (2137221352289 / 1000000) (59891 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4858357 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4858357 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell037 :
    ∀ t ∈ Set.Icc ((437 / 2000) : ℝ) (219 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1548056077 / 1000000000) : ℝ) ≤ Real.exp (2 * (437 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (437 / 2000)) (1548056077 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((219 / 1000) : ℝ)) ≤ (387401227 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (219 / 1000)) (387401227 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((27107683421 / 12500) : ℝ) ≤ Real.exp (3 * (2431609 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2431609 / 500000)) (27107683421 / 12500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((437 / 2000) : ℝ) (219 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2431609 / 500000) (4868239 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (437 / 2000) (219 / 1000) (1548056077 / 1000000000) (387401227 / 250000000) (2431609 / 500000) (4868239 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (437 / 2000) (219 / 1000) (2431609 / 500000) (4868239 / 1000000) (32697 / 500) (3281 / 50)
    (282111 / 1000) (143253 / 500) (-41809 / 250) (27349 / 1000000) (2246713 / 250) (3689 / 31250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2431609 / 500000) (27107683421 / 12500) (3689 / 31250000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2431609 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2431609 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell038 :
    ∀ t ∈ Set.Icc ((219 / 1000) : ℝ) (439 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1549604907 / 1000000000) : ℝ) ≤ Real.exp (2 * (219 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (219 / 1000)) (1549604907 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((439 / 2000) : ℝ)) ≤ (193894411 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (439 / 2000)) (193894411 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((440099098969 / 200000) : ℝ) ≤ Real.exp (3 * (4868083 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4868083 / 1000000)) (440099098969 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((219 / 1000) : ℝ) (439 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4868083 / 1000000) (487311 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (219 / 1000) (439 / 2000) (1549604907 / 1000000000) (193894411 / 125000000) (4868083 / 1000000) (487311 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (219 / 1000) (439 / 2000) (4868083 / 1000000) (487311 / 100000) (32777 / 500) (65781 / 1000)
    (70881 / 250) (71983 / 250) (-162267 / 1000) (13517 / 500000) (9022873 / 1000) (58169 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4868083 / 1000000) (440099098969 / 200000) (58169 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4868083 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4868083 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell039 :
    ∀ t ∈ Set.Icc ((439 / 2000) : ℝ) (11 / 50), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1551155287 / 1000000000) : ℝ) ≤ Real.exp (2 * (439 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (439 / 2000)) (1551155287 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((11 / 50) : ℝ)) ≤ (1552707219 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (11 / 50)) (1552707219 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2232885147889 / 1000000) : ℝ) ≤ Real.exp (3 * (2436477 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2436477 / 500000)) (2232885147889 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((439 / 2000) : ℝ) (11 / 50),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2436477 / 500000) (975597 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (439 / 2000) (11 / 50) (1551155287 / 1000000000) (1552707219 / 1000000000) (2436477 / 500000) (975597 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (439 / 2000) (11 / 50) (2436477 / 500000) (975597 / 200000) (32857 / 500) (32971 / 500)
    (56989 / 200) (289363 / 1000) (-157271 / 1000) (13361 / 500000) (9059033 / 1000) (2293 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2436477 / 500000) (2232885147889 / 1000000) (2293 / 20000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2436477 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2436477 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityUpperExpCompact_cellsBatch001 :
    ∀ t ∈ Set.Icc ((21 / 100) : ℝ) (11 / 50),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell020
      hpThetaDensityUpperExpCompact_cell021)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell022
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell023
      hpThetaDensityUpperExpCompact_cell024)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell025
      hpThetaDensityUpperExpCompact_cell026)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell027
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell028
      hpThetaDensityUpperExpCompact_cell029))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell030
      hpThetaDensityUpperExpCompact_cell031)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell032
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell033
      hpThetaDensityUpperExpCompact_cell034)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell035
      hpThetaDensityUpperExpCompact_cell036)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell037
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell038
      hpThetaDensityUpperExpCompact_cell039)))))

#print axioms hpThetaDensityUpperExpCompact_cellsBatch001
end HodgeProofHP
