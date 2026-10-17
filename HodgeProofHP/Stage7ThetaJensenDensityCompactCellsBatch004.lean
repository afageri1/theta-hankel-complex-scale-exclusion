/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityCurvatureRationalCells

/-! Exact rational certificates with a full infinite-series remainder bound. -/
noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell080 :
    ∀ t ∈ Set.Icc ((17 / 100) : ℝ) (681 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((140494759 / 100000000) : ℝ) ≤ Real.exp (2 * (17 / 100)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (17 / 100)) (140494759 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((681 / 4000) : ℝ)) ≤ (1405650241 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (681 / 4000)) (1405650241 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((281466845543 / 500000) : ℝ) ≤ Real.exp (3 * (2206821 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2206821 / 500000)) (281466845543 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((17 / 100) : ℝ) (681 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2206821 / 500000) (4415991 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (17 / 100) (681 / 4000) (140494759 / 100000000) (1405650241 / 1000000000) (2206821 / 500000) (4415991 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (17 / 100) (681 / 4000) (2206821 / 500000) (4415991 / 1000000) (6428 / 125) (51523 / 1000)
    (33801 / 200) (85381 / 500) (-98573 / 200) (689 / 250) (608461 / 100) (454761 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2206821 / 500000) (281466845543 / 500000) (454761 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2206821 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2206821 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell081 :
    ∀ t ∈ Set.Icc ((681 / 4000) : ℝ) (341 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((4392657 / 3125000) : ℝ) ≤ Real.exp (2 * (681 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (681 / 4000)) (4392657 / 3125000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((341 / 2000) : ℝ)) ≤ (1406353241 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (341 / 2000)) (1406353241 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((35417180761 / 62500) : ℝ) ≤ Real.exp (3 * (88317 / 20000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (88317 / 20000)) (35417180761 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((681 / 4000) : ℝ) (341 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (88317 / 20000) (22091 / 5000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (681 / 4000) (341 / 2000) (4392657 / 3125000) (1406353241 / 1000000000) (88317 / 20000) (22091 / 5000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (681 / 4000) (341 / 2000) (88317 / 20000) (22091 / 5000) (51489 / 1000) (51587 / 1000)
    (84743 / 500) (34249 / 200) (-492003 / 1000) (69 / 25) (3048397 / 500) (451759 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (88317 / 20000) (35417180761 / 62500) (451759 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (88317 / 20000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (88317 / 20000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell082 :
    ∀ t ∈ Set.Icc ((341 / 2000) : ℝ) (683 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((35158831 / 25000000) : ℝ) ≤ Real.exp (2 * (341 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (341 / 2000)) (35158831 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((683 / 4000) : ℝ)) ≤ (703528297 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (683 / 4000)) (703528297 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((22817638259 / 40000) : ℝ) ≤ Real.exp (3 * (2209029 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2209029 / 500000)) (22817638259 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((341 / 2000) : ℝ) (683 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2209029 / 500000) (4420409 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (341 / 2000) (683 / 4000) (35158831 / 25000000) (703528297 / 500000000) (2209029 / 500000) (4420409 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (341 / 2000) (683 / 4000) (2209029 / 500000) (4420409 / 1000000) (25777 / 500) (12913 / 250)
    (169967 / 1000) (21466 / 125) (-61392 / 125) (691 / 250) (1527249 / 250) (56097 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2209029 / 500000) (22817638259 / 40000) (56097 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2209029 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2209029 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell083 :
    ∀ t ∈ Set.Icc ((683 / 4000) : ℝ) (171 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1407056593 / 1000000000) : ℝ) ≤ Real.exp (2 * (683 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (683 / 4000)) (1407056593 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((171 / 1000) : ℝ)) ≤ (703880149 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (171 / 1000)) (703880149 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((574235494569 / 1000000) : ℝ) ≤ Real.exp (3 * (1105067 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1105067 / 250000)) (574235494569 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((683 / 4000) : ℝ) (171 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1105067 / 250000) (221131 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (683 / 4000) (171 / 1000) (1407056593 / 1000000000) (703880149 / 500000000) (1105067 / 250000) (221131 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (683 / 4000) (171 / 1000) (1105067 / 250000) (221131 / 50000) (51619 / 1000) (51717 / 1000)
    (170449 / 1000) (172213 / 1000) (-490263 / 1000) (2769 / 1000) (6121227 / 1000) (445811 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1105067 / 250000) (574235494569 / 1000000) (445811 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1105067 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1105067 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell084 :
    ∀ t ∈ Set.Icc ((171 / 1000) : ℝ) (137 / 800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1407760297 / 1000000000) : ℝ) ≤ Real.exp (2 * (171 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (171 / 1000)) (1407760297 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((137 / 800) : ℝ)) ≤ (704232177 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (137 / 800)) (704232177 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((289027636621 / 500000) : ℝ) ≤ Real.exp (3 * (2211239 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2211239 / 500000)) (289027636621 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((171 / 1000) : ℝ) (137 / 800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2211239 / 500000) (69138 / 15625) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (171 / 1000) (137 / 800) (1407760297 / 1000000000) (704232177 / 500000000) (2211239 / 500000) (69138 / 15625) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (171 / 1000) (137 / 800) (2211239 / 500000) (69138 / 15625) (12921 / 250) (25891 / 500)
    (42733 / 250) (172699 / 1000) (-489377 / 1000) (2773 / 1000) (6133483 / 1000) (88573 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2211239 / 500000) (289027636621 / 500000) (88573 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2211239 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2211239 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell085 :
    ∀ t ∈ Set.Icc ((137 / 800) : ℝ) (343 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1408464353 / 1000000000) : ℝ) ≤ Real.exp (2 * (137 / 800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (137 / 800)) (1408464353 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((343 / 2000) : ℝ)) ≤ (704584381 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (343 / 2000)) (704584381 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2327615807 / 4000) : ℝ) ≤ Real.exp (3 * (442469 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (442469 / 100000)) (2327615807 / 4000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((137 / 800) : ℝ) (343 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (442469 / 100000) (885409 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (137 / 800) (343 / 2000) (1408464353 / 1000000000) (704584381 / 500000000) (442469 / 100000) (885409 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (137 / 800) (343 / 2000) (442469 / 100000) (885409 / 200000) (51749 / 1000) (51847 / 1000)
    (21427 / 125) (34637 / 200) (-122123 / 250) (2777 / 1000) (3072881 / 500) (3437 / 7812500)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (442469 / 100000) (2327615807 / 4000) (3437 / 7812500)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (442469 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (442469 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell086 :
    ∀ t ∈ Set.Icc ((343 / 2000) : ℝ) (687 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1409168761 / 1000000000) : ℝ) ≤ Real.exp (2 * (343 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (343 / 2000)) (1409168761 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((687 / 4000) : ℝ)) ≤ (1409873523 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (687 / 4000)) (1409873523 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((117156002303 / 200000) : ℝ) ≤ Real.exp (3 * (4426903 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4426903 / 1000000)) (117156002303 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((343 / 2000) : ℝ) (687 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4426903 / 1000000) (4429259 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (343 / 2000) (687 / 4000) (1409168761 / 1000000000) (1409873523 / 1000000000) (4426903 / 1000000) (4429259 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (343 / 2000) (687 / 4000) (4426903 / 1000000) (4429259 / 1000000) (25907 / 500) (6489 / 125)
    (85951 / 500) (173673 / 1000) (-487601 / 1000) (2781 / 1000) (3079033 / 500) (17481 / 40000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4426903 / 1000000) (117156002303 / 200000) (17481 / 40000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4426903 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4426903 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell087 :
    ∀ t ∈ Set.Icc ((687 / 4000) : ℝ) (43 / 250), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((704936761 / 500000000) : ℝ) ≤ Real.exp (2 * (687 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (687 / 4000)) (704936761 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43 / 250) : ℝ)) ≤ (352644659 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43 / 250)) (352644659 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((117936731649 / 200000) : ℝ) ≤ Real.exp (3 * (4429117 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4429117 / 1000000)) (117936731649 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((687 / 4000) : ℝ) (43 / 250),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4429117 / 1000000) (2215737 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (687 / 4000) (43 / 250) (704936761 / 500000000) (352644659 / 250000000) (4429117 / 1000000) (2215737 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (687 / 4000) (43 / 250) (4429117 / 1000000) (2215737 / 500000) (51879 / 1000) (25989 / 500)
    (43097 / 250) (174161 / 1000) (-60838 / 125) (557 / 200) (6170393 / 1000) (108533 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4429117 / 1000000) (117936731649 / 200000) (108533 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4429117 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4429117 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell088 :
    ∀ t ∈ Set.Icc ((43 / 250) : ℝ) (689 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((282115727 / 200000000) : ℝ) ≤ Real.exp (2 * (43 / 250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43 / 250)) (282115727 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((689 / 4000) : ℝ)) ≤ (705642051 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (689 / 4000)) (705642051 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((593615099271 / 1000000) : ℝ) ≤ Real.exp (3 * (1107833 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1107833 / 250000)) (593615099271 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43 / 250) : ℝ) (689 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1107833 / 250000) (4433691 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43 / 250) (689 / 4000) (282115727 / 200000000) (705642051 / 500000000) (1107833 / 250000) (4433691 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (43 / 250) (689 / 4000) (1107833 / 250000) (4433691 / 1000000) (6493 / 125) (52043 / 1000)
    (1383 / 8) (174651 / 1000) (-242897 / 500) (2789 / 1000) (24731 / 4) (53907 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1107833 / 250000) (593615099271 / 1000000) (53907 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1107833 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1107833 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell089 :
    ∀ t ∈ Set.Icc ((689 / 4000) : ℝ) (69 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1411284101 / 1000000000) : ℝ) ≤ Real.exp (2 * (689 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (689 / 4000)) (1411284101 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((69 / 400) : ℝ)) ≤ (8824937 / 6250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (69 / 400)) (8824937 / 6250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((298788168127 / 500000) : ℝ) ≤ Real.exp (3 * (4433549 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4433549 / 1000000)) (298788168127 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((689 / 4000) : ℝ) (69 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4433549 / 1000000) (1108977 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (689 / 4000) (69 / 400) (1411284101 / 1000000000) (8824937 / 6250000) (4433549 / 1000000) (1108977 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (689 / 4000) (69 / 400) (4433549 / 1000000) (1108977 / 250000) (52009 / 1000) (13027 / 250)
    (43341 / 250) (175141 / 1000) (-121223 / 250) (1397 / 500) (3097563 / 500) (214199 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4433549 / 1000000) (298788168127 / 500000) (214199 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4433549 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4433549 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell090 :
    ∀ t ∈ Set.Icc ((69 / 400) : ℝ) (691 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1411989919 / 1000000000) : ℝ) ≤ Real.exp (2 * (69 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (69 / 400)) (1411989919 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((691 / 4000) : ℝ)) ≤ (353174023 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (691 / 4000)) (353174023 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((300782003181 / 500000) : ℝ) ≤ Real.exp (3 * (2217883 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2217883 / 500000)) (300782003181 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((69 / 400) : ℝ) (691 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2217883 / 500000) (4438127 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (69 / 400) (691 / 4000) (1411989919 / 1000000000) (353174023 / 250000000) (2217883 / 500000) (4438127 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (69 / 400) (691 / 4000) (2217883 / 500000) (4438127 / 1000000) (2083 / 40) (26087 / 500)
    (173853 / 1000) (175633 / 1000) (-48397 / 100) (1399 / 500) (6207531 / 1000) (212779 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2217883 / 500000) (300782003181 / 500000) (212779 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2217883 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2217883 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell091 :
    ∀ t ∈ Set.Icc ((691 / 4000) : ℝ) (173 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1412696091 / 1000000000) : ℝ) ≤ Real.exp (2 * (691 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (691 / 4000)) (1412696091 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((173 / 1000) : ℝ)) ≤ (176675327 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (173 / 1000)) (176675327 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((18924378209 / 31250) : ℝ) ≤ Real.exp (3 * (138687 / 31250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (138687 / 31250)) (18924378209 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((691 / 4000) : ℝ) (173 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (138687 / 31250) (2220173 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (691 / 4000) (173 / 1000) (1412696091 / 1000000000) (176675327 / 125000000) (138687 / 31250) (2220173 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (691 / 4000) (173 / 1000) (138687 / 31250) (2220173 / 500000) (2607 / 50) (52239 / 1000)
    (174343 / 1000) (1409 / 8) (-9661 / 20) (1401 / 500) (1243991 / 200) (26421 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (138687 / 31250) (18924378209 / 31250) (26421 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (138687 / 31250)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (138687 / 31250)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell092 :
    ∀ t ∈ Set.Icc ((173 / 1000) : ℝ) (693 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((282680523 / 200000000) : ℝ) ≤ Real.exp (2 * (173 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (173 / 1000)) (282680523 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((693 / 4000) : ℝ)) ≤ (707054747 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (693 / 4000)) (707054747 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((609626668021 / 1000000) : ℝ) ≤ Real.exp (3 * (1110051 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1110051 / 250000)) (609626668021 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((173 / 1000) : ℝ) (693 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1110051 / 250000) (4442567 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (173 / 1000) (693 / 4000) (282680523 / 200000000) (707054747 / 500000000) (1110051 / 250000) (4442567 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (173 / 1000) (693 / 4000) (1110051 / 250000) (4442567 / 1000000) (26103 / 500) (10461 / 200)
    (87417 / 500) (176619 / 1000) (-241061 / 500) (1403 / 500) (6232409 / 1000) (41993 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1110051 / 250000) (609626668021 / 1000000) (41993 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1110051 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1110051 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell093 :
    ∀ t ∈ Set.Icc ((693 / 4000) : ℝ) (347 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1414109493 / 1000000000) : ℝ) ≤ Real.exp (2 * (693 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (693 / 4000)) (1414109493 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((347 / 2000) : ℝ)) ≤ (707408363 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (347 / 2000)) (707408363 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((613700272511 / 1000000) : ℝ) ≤ Real.exp (3 * (555303 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (555303 / 125000)) (613700272511 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((693 / 4000) : ℝ) (347 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (555303 / 125000) (4444789 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (693 / 4000) (347 / 2000) (1414109493 / 1000000000) (707408363 / 500000000) (555303 / 125000) (4444789 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (693 / 4000) (347 / 2000) (555303 / 125000) (4444789 / 1000000) (52271 / 1000) (52371 / 1000)
    (87663 / 500) (88557 / 500) (-481183 / 1000) (281 / 100) (6244887 / 1000) (208571 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (555303 / 125000) (613700272511 / 1000000) (208571 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (555303 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (555303 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell094 :
    ∀ t ∈ Set.Icc ((347 / 2000) : ℝ) (139 / 800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((56592669 / 40000000) : ℝ) ≤ Real.exp (2 * (347 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (347 / 2000)) (56592669 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((139 / 800) : ℝ)) ≤ (1415524311 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (139 / 800)) (1415524311 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((617804803587 / 1000000) : ℝ) ≤ Real.exp (3 * (2222323 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2222323 / 500000)) (617804803587 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((347 / 2000) : ℝ) (139 / 800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2222323 / 500000) (1111753 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (347 / 2000) (139 / 800) (56592669 / 40000000) (1415524311 / 1000000000) (2222323 / 500000) (1111753 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (347 / 2000) (139 / 800) (2222323 / 500000) (1111753 / 250000) (52337 / 1000) (13109 / 250)
    (175819 / 1000) (177609 / 1000) (-480243 / 1000) (563 / 200) (625739 / 100) (414371 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2222323 / 500000) (617804803587 / 1000000) (414371 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2222323 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2222323 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell095 :
    ∀ t ∈ Set.Icc ((139 / 800) : ℝ) (87 / 500), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((141552431 / 100000000) : ℝ) ≤ Real.exp (2 * (139 / 800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (139 / 800)) (141552431 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((87 / 500) : ℝ)) ≤ (5664929 / 4000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (87 / 500)) (5664929 / 4000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((310969325853 / 500000) : ℝ) ≤ Real.exp (3 * (4446869 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4446869 / 1000000)) (310969325853 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((139 / 800) : ℝ) (87 / 500),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4446869 / 1000000) (1112309 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (139 / 800) (87 / 500) (141552431 / 100000000) (5664929 / 4000000) (4446869 / 1000000) (1112309 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (139 / 800) (87 / 500) (4446869 / 1000000) (1112309 / 250000) (52403 / 1000) (26251 / 500)
    (88157 / 500) (89053 / 500) (-239649 / 500) (2819 / 1000) (6269917 / 1000) (411617 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4446869 / 1000000) (310969325853 / 500000) (411617 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4446869 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4446869 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell096 :
    ∀ t ∈ Set.Icc ((87 / 500) : ℝ) (697 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1416232249 / 1000000000) : ℝ) ≤ Real.exp (2 * (87 / 500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (87 / 500)) (1416232249 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((697 / 4000) : ℝ)) ≤ (1416940543 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (697 / 4000)) (1416940543 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((626102037909 / 1000000) : ℝ) ≤ Real.exp (3 * (4449093 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4449093 / 1000000)) (626102037909 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((87 / 500) : ℝ) (697 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4449093 / 1000000) (4451461 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (87 / 500) (697 / 4000) (1416232249 / 1000000000) (1416940543 / 1000000000) (4449093 / 1000000) (4451461 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (87 / 500) (697 / 4000) (4449093 / 1000000) (4451461 / 1000000) (13117 / 250) (6571 / 125)
    (176809 / 1000) (178603 / 1000) (-478347 / 1000) (2823 / 1000) (1570617 / 250) (5111 / 12500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4449093 / 1000000) (626102037909 / 1000000) (5111 / 12500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4449093 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4449093 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell097 :
    ∀ t ∈ Set.Icc ((697 / 4000) : ℝ) (349 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((708470271 / 500000000) : ℝ) ≤ Real.exp (2 * (697 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (697 / 4000)) (708470271 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((349 / 2000) : ℝ)) ≤ (1417649191 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (349 / 2000)) (1417649191 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31514759249 / 50000) : ℝ) ≤ Real.exp (3 * (2225659 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2225659 / 500000)) (31514759249 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((697 / 4000) : ℝ) (349 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2225659 / 500000) (4453687 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (697 / 4000) (349 / 2000) (708470271 / 500000000) (1417649191 / 1000000000) (2225659 / 500000) (4453687 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (697 / 4000) (349 / 2000) (2225659 / 500000) (4453687 / 1000000) (26267 / 500) (26317 / 500)
    (35461 / 200) (89551 / 500) (-477389 / 1000) (2827 / 1000) (1573761 / 250) (406159 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2225659 / 500000) (31514759249 / 50000) (406159 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2225659 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2225659 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell098 :
    ∀ t ∈ Set.Icc ((349 / 2000) : ℝ) (699 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((141764919 / 100000000) : ℝ) ≤ Real.exp (2 * (349 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (349 / 2000)) (141764919 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((699 / 4000) : ℝ)) ≤ (1418358193 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (699 / 4000)) (1418358193 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((126903663493 / 200000) : ℝ) ≤ Real.exp (3 * (556693 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (556693 / 125000)) (126903663493 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((349 / 2000) : ℝ) (699 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (556693 / 125000) (891183 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (349 / 2000) (699 / 4000) (141764919 / 100000000) (1418358193 / 1000000000) (556693 / 125000) (891183 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (349 / 2000) (699 / 4000) (556693 / 125000) (891183 / 200000) (263 / 5) (527 / 10)
    (88901 / 500) (89801 / 500) (-238209 / 500) (354 / 125) (126153 / 20) (788 / 1953125)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (556693 / 125000) (126903663493 / 200000) (788 / 1953125)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (556693 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (556693 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell099 :
    ∀ t ∈ Set.Icc ((699 / 4000) : ℝ) (7 / 40), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((88647387 / 62500000) : ℝ) ≤ Real.exp (2 * (699 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (699 / 4000)) (88647387 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((7 / 40) : ℝ)) ≤ (1419067549 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (7 / 40)) (1419067549 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((638773577971 / 1000000) : ℝ) ≤ Real.exp (3 * (1113943 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1113943 / 250000)) (638773577971 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((699 / 4000) : ℝ) (7 / 40),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1113943 / 250000) (4458143 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (699 / 4000) (7 / 40) (88647387 / 62500000) (1419067549 / 1000000000) (1113943 / 250000) (4458143 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (699 / 4000) (7 / 40) (1113943 / 250000) (4458143 / 1000000) (26333 / 500) (26383 / 500)
    (178301 / 1000) (90051 / 500) (-95091 / 200) (709 / 250) (252811 / 40) (3131 / 7812500)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1113943 / 250000) (638773577971 / 1000000) (3131 / 7812500)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1113943 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1113943 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityCompact_cellsBatch004 :
    ∀ t ∈ Set.Icc ((17 / 100) : ℝ) (7 / 40),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell080
      hpThetaDensityCompact_cell081)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell082
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell083
      hpThetaDensityCompact_cell084)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell085
      hpThetaDensityCompact_cell086)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell087
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell088
      hpThetaDensityCompact_cell089))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell090
      hpThetaDensityCompact_cell091)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell092
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell093
      hpThetaDensityCompact_cell094)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell095
      hpThetaDensityCompact_cell096)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell097
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell098
      hpThetaDensityCompact_cell099)))))

#print axioms hpThetaDensityCompact_cellsBatch004
end HodgeProofHP
